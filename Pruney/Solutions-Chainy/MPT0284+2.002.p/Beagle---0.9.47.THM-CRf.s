%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 5.87s
% Output     : CNFRefutation 5.87s
% Verified   : 
% Statistics : Number of formulae       :   61 (  99 expanded)
%              Number of leaves         :   27 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 107 expanded)
%              Number of equality atoms :   27 (  52 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_437,plain,(
    ! [A_66,B_67] : k2_xboole_0(k4_xboole_0(A_66,B_67),k4_xboole_0(B_67,A_66)) = k5_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_102,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(B_44,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_102])).

tff(c_28,plain,(
    ! [A_25,B_26] : k3_tarski(k2_tarski(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_150,plain,(
    ! [B_44,A_43] : k2_xboole_0(B_44,A_43) = k2_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_28])).

tff(c_5883,plain,(
    ! [B_166,A_167] : k2_xboole_0(k4_xboole_0(B_166,A_167),k4_xboole_0(A_167,B_166)) = k5_xboole_0(A_167,B_166) ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_150])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5969,plain,(
    ! [B_168,A_169] : k5_xboole_0(B_168,A_169) = k5_xboole_0(A_169,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_5883,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_201,plain,(
    ! [A_47,B_48] : k5_xboole_0(A_47,k3_xboole_0(A_47,B_48)) = k4_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_125,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_117])).

tff(c_754,plain,(
    ! [A_81,B_82,C_83] : k5_xboole_0(k3_xboole_0(A_81,B_82),k3_xboole_0(C_83,B_82)) = k3_xboole_0(k5_xboole_0(A_81,C_83),B_82) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_809,plain,(
    ! [B_6,C_83] : k5_xboole_0(B_6,k3_xboole_0(C_83,B_6)) = k3_xboole_0(k5_xboole_0(B_6,C_83),B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_754])).

tff(c_841,plain,(
    ! [B_84,C_85] : k3_xboole_0(B_84,k5_xboole_0(B_84,C_85)) = k4_xboole_0(B_84,C_85) ),
    inference(demodulation,[status(thm),theory(equality)],[c_213,c_2,c_809])).

tff(c_238,plain,(
    ! [A_52,B_53] : k4_xboole_0(A_52,k4_xboole_0(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_14,B_15] : r1_tarski(k4_xboole_0(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_256,plain,(
    ! [A_54,B_55] : r1_tarski(k3_xboole_0(A_54,B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_18])).

tff(c_267,plain,(
    ! [B_2,A_1] : r1_tarski(k3_xboole_0(B_2,A_1),A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_256])).

tff(c_871,plain,(
    ! [B_84,C_85] : r1_tarski(k4_xboole_0(B_84,C_85),k5_xboole_0(B_84,C_85)) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_267])).

tff(c_6042,plain,(
    ! [A_169,B_168] : r1_tarski(k4_xboole_0(A_169,B_168),k5_xboole_0(B_168,A_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5969,c_871])).

tff(c_30,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k1_zfmisc_1(A_27),k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_510,plain,(
    ! [A_72,C_73,B_74] :
      ( r1_tarski(k2_xboole_0(A_72,C_73),B_74)
      | ~ r1_tarski(C_73,B_74)
      | ~ r1_tarski(A_72,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_529,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_510,c_32])).

tff(c_1009,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_529])).

tff(c_1141,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_1009])).

tff(c_1145,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_871,c_1141])).

tff(c_1146,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_529])).

tff(c_1263,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_1146])).

tff(c_6261,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_1263])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.87/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.22  
% 5.87/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.22  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.87/2.22  
% 5.87/2.22  %Foreground sorts:
% 5.87/2.22  
% 5.87/2.22  
% 5.87/2.22  %Background operators:
% 5.87/2.22  
% 5.87/2.22  
% 5.87/2.22  %Foreground operators:
% 5.87/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.87/2.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.87/2.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.87/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.87/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.87/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.87/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.87/2.22  tff('#skF_1', type, '#skF_1': $i).
% 5.87/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.87/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.87/2.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.87/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.87/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.87/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.87/2.22  
% 5.87/2.23  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.87/2.23  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.87/2.23  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.87/2.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.87/2.23  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.87/2.23  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.87/2.23  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.87/2.23  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 5.87/2.23  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.87/2.23  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.87/2.23  tff(f_63, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 5.87/2.23  tff(f_53, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.87/2.23  tff(f_66, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 5.87/2.23  tff(c_437, plain, (![A_66, B_67]: (k2_xboole_0(k4_xboole_0(A_66, B_67), k4_xboole_0(B_67, A_66))=k5_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.87/2.23  tff(c_24, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.87/2.23  tff(c_102, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.87/2.23  tff(c_144, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(B_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_24, c_102])).
% 5.87/2.23  tff(c_28, plain, (![A_25, B_26]: (k3_tarski(k2_tarski(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.87/2.23  tff(c_150, plain, (![B_44, A_43]: (k2_xboole_0(B_44, A_43)=k2_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_144, c_28])).
% 5.87/2.23  tff(c_5883, plain, (![B_166, A_167]: (k2_xboole_0(k4_xboole_0(B_166, A_167), k4_xboole_0(A_167, B_166))=k5_xboole_0(A_167, B_166))), inference(superposition, [status(thm), theory('equality')], [c_437, c_150])).
% 5.87/2.23  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.87/2.23  tff(c_5969, plain, (![B_168, A_169]: (k5_xboole_0(B_168, A_169)=k5_xboole_0(A_169, B_168))), inference(superposition, [status(thm), theory('equality')], [c_5883, c_4])).
% 5.87/2.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.87/2.23  tff(c_201, plain, (![A_47, B_48]: (k5_xboole_0(A_47, k3_xboole_0(A_47, B_48))=k4_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.87/2.23  tff(c_213, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_201])).
% 5.87/2.23  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.87/2.23  tff(c_117, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.87/2.23  tff(c_125, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_117])).
% 5.87/2.23  tff(c_754, plain, (![A_81, B_82, C_83]: (k5_xboole_0(k3_xboole_0(A_81, B_82), k3_xboole_0(C_83, B_82))=k3_xboole_0(k5_xboole_0(A_81, C_83), B_82))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.87/2.23  tff(c_809, plain, (![B_6, C_83]: (k5_xboole_0(B_6, k3_xboole_0(C_83, B_6))=k3_xboole_0(k5_xboole_0(B_6, C_83), B_6))), inference(superposition, [status(thm), theory('equality')], [c_125, c_754])).
% 5.87/2.23  tff(c_841, plain, (![B_84, C_85]: (k3_xboole_0(B_84, k5_xboole_0(B_84, C_85))=k4_xboole_0(B_84, C_85))), inference(demodulation, [status(thm), theory('equality')], [c_213, c_2, c_809])).
% 5.87/2.23  tff(c_238, plain, (![A_52, B_53]: (k4_xboole_0(A_52, k4_xboole_0(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.87/2.23  tff(c_18, plain, (![A_14, B_15]: (r1_tarski(k4_xboole_0(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.87/2.23  tff(c_256, plain, (![A_54, B_55]: (r1_tarski(k3_xboole_0(A_54, B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_238, c_18])).
% 5.87/2.23  tff(c_267, plain, (![B_2, A_1]: (r1_tarski(k3_xboole_0(B_2, A_1), A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_256])).
% 5.87/2.23  tff(c_871, plain, (![B_84, C_85]: (r1_tarski(k4_xboole_0(B_84, C_85), k5_xboole_0(B_84, C_85)))), inference(superposition, [status(thm), theory('equality')], [c_841, c_267])).
% 5.87/2.23  tff(c_6042, plain, (![A_169, B_168]: (r1_tarski(k4_xboole_0(A_169, B_168), k5_xboole_0(B_168, A_169)))), inference(superposition, [status(thm), theory('equality')], [c_5969, c_871])).
% 5.87/2.23  tff(c_30, plain, (![A_27, B_28]: (r1_tarski(k1_zfmisc_1(A_27), k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.87/2.23  tff(c_510, plain, (![A_72, C_73, B_74]: (r1_tarski(k2_xboole_0(A_72, C_73), B_74) | ~r1_tarski(C_73, B_74) | ~r1_tarski(A_72, B_74))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.87/2.23  tff(c_32, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.87/2.23  tff(c_529, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_510, c_32])).
% 5.87/2.23  tff(c_1009, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_529])).
% 5.87/2.23  tff(c_1141, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1009])).
% 5.87/2.23  tff(c_1145, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_871, c_1141])).
% 5.87/2.23  tff(c_1146, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_529])).
% 5.87/2.23  tff(c_1263, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1146])).
% 5.87/2.23  tff(c_6261, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6042, c_1263])).
% 5.87/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.87/2.23  
% 5.87/2.23  Inference rules
% 5.87/2.23  ----------------------
% 5.87/2.23  #Ref     : 0
% 5.87/2.23  #Sup     : 1621
% 5.87/2.23  #Fact    : 0
% 5.87/2.23  #Define  : 0
% 5.87/2.23  #Split   : 2
% 5.87/2.23  #Chain   : 0
% 5.87/2.23  #Close   : 0
% 5.87/2.23  
% 5.87/2.23  Ordering : KBO
% 5.87/2.23  
% 5.87/2.23  Simplification rules
% 5.87/2.23  ----------------------
% 5.87/2.23  #Subsume      : 116
% 5.87/2.23  #Demod        : 1464
% 5.87/2.23  #Tautology    : 716
% 5.87/2.23  #SimpNegUnit  : 0
% 5.87/2.23  #BackRed      : 1
% 5.87/2.23  
% 5.87/2.23  #Partial instantiations: 0
% 5.87/2.23  #Strategies tried      : 1
% 5.87/2.23  
% 5.87/2.23  Timing (in seconds)
% 5.87/2.24  ----------------------
% 5.87/2.24  Preprocessing        : 0.30
% 5.87/2.24  Parsing              : 0.17
% 5.87/2.24  CNF conversion       : 0.02
% 5.87/2.24  Main loop            : 1.16
% 5.87/2.24  Inferencing          : 0.30
% 5.87/2.24  Reduction            : 0.57
% 5.87/2.24  Demodulation         : 0.49
% 5.87/2.24  BG Simplification    : 0.04
% 5.87/2.24  Subsumption          : 0.18
% 5.87/2.24  Abstraction          : 0.06
% 5.87/2.24  MUC search           : 0.00
% 5.87/2.24  Cooper               : 0.00
% 5.87/2.24  Total                : 1.49
% 5.87/2.24  Index Insertion      : 0.00
% 5.87/2.24  Index Deletion       : 0.00
% 5.87/2.24  Index Matching       : 0.00
% 5.87/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
