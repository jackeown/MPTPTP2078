%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:27 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   63 (  93 expanded)
%              Number of leaves         :   26 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 ( 101 expanded)
%              Number of equality atoms :   29 (  48 expanded)
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

tff(f_53,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_22,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_170,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(B_44,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_26,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_176,plain,(
    ! [B_44,A_43] : k2_xboole_0(B_44,A_43) = k2_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_26])).

tff(c_275,plain,(
    ! [A_54,B_55] : k2_xboole_0(k4_xboole_0(A_54,B_55),k4_xboole_0(B_55,A_54)) = k5_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5581,plain,(
    ! [B_163,A_164] : k2_xboole_0(k4_xboole_0(B_163,A_164),k4_xboole_0(A_164,B_163)) = k5_xboole_0(A_164,B_163) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_275])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(B_4,A_3)) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5732,plain,(
    ! [B_168,A_169] : k5_xboole_0(B_168,A_169) = k5_xboole_0(A_169,B_168) ),
    inference(superposition,[status(thm),theory(equality)],[c_5581,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_232,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_244,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_131,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_143,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_131])).

tff(c_1075,plain,(
    ! [A_84,B_85,C_86] : k5_xboole_0(k3_xboole_0(A_84,B_85),k3_xboole_0(C_86,B_85)) = k3_xboole_0(k5_xboole_0(A_84,C_86),B_85) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1124,plain,(
    ! [B_6,C_86] : k5_xboole_0(B_6,k3_xboole_0(C_86,B_6)) = k3_xboole_0(k5_xboole_0(B_6,C_86),B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_1075])).

tff(c_1156,plain,(
    ! [B_87,C_88] : k3_xboole_0(B_87,k5_xboole_0(B_87,C_88)) = k4_xboole_0(B_87,C_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_244,c_1124])).

tff(c_67,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_16])).

tff(c_1195,plain,(
    ! [B_87,C_88] : r1_tarski(k4_xboole_0(B_87,C_88),k5_xboole_0(B_87,C_88)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1156,c_82])).

tff(c_5801,plain,(
    ! [A_169,B_168] : r1_tarski(k4_xboole_0(A_169,B_168),k5_xboole_0(B_168,A_169)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5732,c_1195])).

tff(c_28,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(k1_zfmisc_1(A_25),k1_zfmisc_1(B_26))
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_742,plain,(
    ! [A_73,B_74,C_75] : k5_xboole_0(k3_xboole_0(A_73,B_74),k3_xboole_0(C_75,B_74)) = k3_xboole_0(k5_xboole_0(A_73,C_75),B_74) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_791,plain,(
    ! [B_6,C_75] : k5_xboole_0(B_6,k3_xboole_0(C_75,B_6)) = k3_xboole_0(k5_xboole_0(B_6,C_75),B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_742])).

tff(c_823,plain,(
    ! [B_76,C_77] : k3_xboole_0(B_76,k5_xboole_0(B_76,C_77)) = k4_xboole_0(B_76,C_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_2,c_791])).

tff(c_862,plain,(
    ! [B_76,C_77] : r1_tarski(k4_xboole_0(B_76,C_77),k5_xboole_0(B_76,C_77)) ),
    inference(superposition,[status(thm),theory(equality)],[c_823,c_82])).

tff(c_516,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_tarski(k2_xboole_0(A_64,C_65),B_66)
      | ~ r1_tarski(C_65,B_66)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_535,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_516,c_30])).

tff(c_575,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_535])).

tff(c_905,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_575])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_905])).

tff(c_909,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_535])).

tff(c_1448,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_909])).

tff(c_5893,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5801,c_1448])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:33:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.13  
% 5.70/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.13  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 5.70/2.13  
% 5.70/2.13  %Foreground sorts:
% 5.70/2.13  
% 5.70/2.13  
% 5.70/2.13  %Background operators:
% 5.70/2.13  
% 5.70/2.13  
% 5.70/2.13  %Foreground operators:
% 5.70/2.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.70/2.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.70/2.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.70/2.13  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.13  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.70/2.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.70/2.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.70/2.13  
% 5.70/2.14  tff(f_53, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.70/2.14  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 5.70/2.14  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_xboole_0)).
% 5.70/2.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.70/2.14  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.70/2.14  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.70/2.14  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.70/2.14  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 5.70/2.14  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.70/2.14  tff(f_61, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 5.70/2.14  tff(f_51, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 5.70/2.14  tff(f_64, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 5.70/2.14  tff(c_22, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.70/2.14  tff(c_115, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.70/2.14  tff(c_170, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(B_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_22, c_115])).
% 5.70/2.14  tff(c_26, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.70/2.14  tff(c_176, plain, (![B_44, A_43]: (k2_xboole_0(B_44, A_43)=k2_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_170, c_26])).
% 5.70/2.14  tff(c_275, plain, (![A_54, B_55]: (k2_xboole_0(k4_xboole_0(A_54, B_55), k4_xboole_0(B_55, A_54))=k5_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.14  tff(c_5581, plain, (![B_163, A_164]: (k2_xboole_0(k4_xboole_0(B_163, A_164), k4_xboole_0(A_164, B_163))=k5_xboole_0(A_164, B_163))), inference(superposition, [status(thm), theory('equality')], [c_176, c_275])).
% 5.70/2.14  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(B_4, A_3))=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.70/2.14  tff(c_5732, plain, (![B_168, A_169]: (k5_xboole_0(B_168, A_169)=k5_xboole_0(A_169, B_168))), inference(superposition, [status(thm), theory('equality')], [c_5581, c_4])).
% 5.70/2.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.14  tff(c_232, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.70/2.14  tff(c_244, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_232])).
% 5.70/2.14  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.14  tff(c_131, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.70/2.14  tff(c_143, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_131])).
% 5.70/2.14  tff(c_1075, plain, (![A_84, B_85, C_86]: (k5_xboole_0(k3_xboole_0(A_84, B_85), k3_xboole_0(C_86, B_85))=k3_xboole_0(k5_xboole_0(A_84, C_86), B_85))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.14  tff(c_1124, plain, (![B_6, C_86]: (k5_xboole_0(B_6, k3_xboole_0(C_86, B_6))=k3_xboole_0(k5_xboole_0(B_6, C_86), B_6))), inference(superposition, [status(thm), theory('equality')], [c_143, c_1075])).
% 5.70/2.14  tff(c_1156, plain, (![B_87, C_88]: (k3_xboole_0(B_87, k5_xboole_0(B_87, C_88))=k4_xboole_0(B_87, C_88))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_244, c_1124])).
% 5.70/2.14  tff(c_67, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.14  tff(c_16, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.70/2.14  tff(c_82, plain, (![B_32, A_33]: (r1_tarski(k3_xboole_0(B_32, A_33), A_33))), inference(superposition, [status(thm), theory('equality')], [c_67, c_16])).
% 5.70/2.14  tff(c_1195, plain, (![B_87, C_88]: (r1_tarski(k4_xboole_0(B_87, C_88), k5_xboole_0(B_87, C_88)))), inference(superposition, [status(thm), theory('equality')], [c_1156, c_82])).
% 5.70/2.14  tff(c_5801, plain, (![A_169, B_168]: (r1_tarski(k4_xboole_0(A_169, B_168), k5_xboole_0(B_168, A_169)))), inference(superposition, [status(thm), theory('equality')], [c_5732, c_1195])).
% 5.70/2.14  tff(c_28, plain, (![A_25, B_26]: (r1_tarski(k1_zfmisc_1(A_25), k1_zfmisc_1(B_26)) | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 5.70/2.14  tff(c_742, plain, (![A_73, B_74, C_75]: (k5_xboole_0(k3_xboole_0(A_73, B_74), k3_xboole_0(C_75, B_74))=k3_xboole_0(k5_xboole_0(A_73, C_75), B_74))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.14  tff(c_791, plain, (![B_6, C_75]: (k5_xboole_0(B_6, k3_xboole_0(C_75, B_6))=k3_xboole_0(k5_xboole_0(B_6, C_75), B_6))), inference(superposition, [status(thm), theory('equality')], [c_143, c_742])).
% 5.70/2.14  tff(c_823, plain, (![B_76, C_77]: (k3_xboole_0(B_76, k5_xboole_0(B_76, C_77))=k4_xboole_0(B_76, C_77))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_2, c_791])).
% 5.70/2.14  tff(c_862, plain, (![B_76, C_77]: (r1_tarski(k4_xboole_0(B_76, C_77), k5_xboole_0(B_76, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_823, c_82])).
% 5.70/2.14  tff(c_516, plain, (![A_64, C_65, B_66]: (r1_tarski(k2_xboole_0(A_64, C_65), B_66) | ~r1_tarski(C_65, B_66) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.70/2.14  tff(c_30, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.70/2.14  tff(c_535, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_516, c_30])).
% 5.70/2.14  tff(c_575, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_535])).
% 5.70/2.14  tff(c_905, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_575])).
% 5.70/2.14  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_862, c_905])).
% 5.70/2.14  tff(c_909, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_535])).
% 5.70/2.14  tff(c_1448, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_909])).
% 5.70/2.14  tff(c_5893, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5801, c_1448])).
% 5.70/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.14  
% 5.70/2.14  Inference rules
% 5.70/2.14  ----------------------
% 5.70/2.14  #Ref     : 0
% 5.70/2.14  #Sup     : 1515
% 5.70/2.14  #Fact    : 0
% 5.70/2.14  #Define  : 0
% 5.70/2.14  #Split   : 2
% 5.70/2.14  #Chain   : 0
% 5.70/2.14  #Close   : 0
% 5.70/2.14  
% 5.70/2.14  Ordering : KBO
% 5.70/2.14  
% 5.70/2.14  Simplification rules
% 5.70/2.14  ----------------------
% 5.70/2.14  #Subsume      : 121
% 5.70/2.14  #Demod        : 1298
% 5.70/2.14  #Tautology    : 658
% 5.70/2.14  #SimpNegUnit  : 0
% 5.70/2.14  #BackRed      : 2
% 5.70/2.14  
% 5.70/2.14  #Partial instantiations: 0
% 5.70/2.14  #Strategies tried      : 1
% 5.70/2.14  
% 5.70/2.14  Timing (in seconds)
% 5.70/2.14  ----------------------
% 5.70/2.15  Preprocessing        : 0.29
% 5.70/2.15  Parsing              : 0.16
% 5.70/2.15  CNF conversion       : 0.02
% 5.70/2.15  Main loop            : 1.08
% 5.70/2.15  Inferencing          : 0.29
% 5.70/2.15  Reduction            : 0.53
% 5.70/2.15  Demodulation         : 0.45
% 5.70/2.15  BG Simplification    : 0.04
% 5.70/2.15  Subsumption          : 0.16
% 5.70/2.15  Abstraction          : 0.06
% 5.70/2.15  MUC search           : 0.00
% 5.70/2.15  Cooper               : 0.00
% 5.70/2.15  Total                : 1.41
% 5.70/2.15  Index Insertion      : 0.00
% 5.70/2.15  Index Deletion       : 0.00
% 5.70/2.15  Index Matching       : 0.00
% 5.70/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
