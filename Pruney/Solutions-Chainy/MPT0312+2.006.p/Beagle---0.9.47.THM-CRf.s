%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:54 EST 2020

% Result     : Theorem 3.02s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 107 expanded)
%              Number of leaves         :   31 (  51 expanded)
%              Depth                    :    9
%              Number of atoms          :   47 (  96 expanded)
%              Number of equality atoms :   40 (  83 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_397,plain,(
    ! [A_70,B_71,C_72] : k5_xboole_0(k5_xboole_0(A_70,B_71),C_72) = k5_xboole_0(A_70,k5_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_861,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k5_xboole_0(B_86,k5_xboole_0(A_85,B_86))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_14])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [A_64,B_65] : k5_xboole_0(k5_xboole_0(A_64,B_65),k2_xboole_0(A_64,B_65)) = k3_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_213,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_13,A_13)) = k3_xboole_0(A_13,A_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_221,plain,(
    ! [A_13] : k5_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_213])).

tff(c_485,plain,(
    ! [A_13,C_72] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_72)) = k5_xboole_0(k1_xboole_0,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_397])).

tff(c_502,plain,(
    ! [A_13,C_72] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_72)) = C_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_221,c_485])).

tff(c_869,plain,(
    ! [B_86,A_85] : k5_xboole_0(B_86,k5_xboole_0(A_85,B_86)) = k5_xboole_0(A_85,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_502])).

tff(c_1007,plain,(
    ! [B_87,A_88] : k5_xboole_0(B_87,k5_xboole_0(A_88,B_87)) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_869])).

tff(c_976,plain,(
    ! [B_86,A_85] : k5_xboole_0(B_86,k5_xboole_0(A_85,B_86)) = A_85 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_869])).

tff(c_1010,plain,(
    ! [A_88,B_87] : k5_xboole_0(k5_xboole_0(A_88,B_87),A_88) = B_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_1007,c_976])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [A_59,B_60] :
      ( k2_xboole_0(A_59,B_60) = B_60
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_142,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_135])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_2])).

tff(c_195,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_147,c_180])).

tff(c_1348,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1010,c_195])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_143,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_135])).

tff(c_198,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_180])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k5_xboole_0(k5_xboole_0(A_10,B_11),C_12) = k5_xboole_0(A_10,k5_xboole_0(B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_589,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_12])).

tff(c_598,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_589])).

tff(c_32,plain,(
    ! [A_45,C_47,B_46,D_48] : k3_xboole_0(k2_zfmisc_1(A_45,C_47),k2_zfmisc_1(B_46,D_48)) = k2_zfmisc_1(k3_xboole_0(A_45,B_46),k3_xboole_0(C_47,D_48)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_603,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_598,c_39])).

tff(c_1351,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1348,c_603])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:55:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.02/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  
% 3.18/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.49  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.18/1.49  
% 3.18/1.49  %Foreground sorts:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Background operators:
% 3.18/1.49  
% 3.18/1.49  
% 3.18/1.49  %Foreground operators:
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.18/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.18/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.18/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.49  
% 3.18/1.50  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.18/1.50  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.18/1.50  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.18/1.50  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.18/1.50  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.18/1.50  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.18/1.50  tff(f_66, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 3.18/1.50  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.18/1.50  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.18/1.50  tff(f_59, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.18/1.50  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.18/1.50  tff(c_397, plain, (![A_70, B_71, C_72]: (k5_xboole_0(k5_xboole_0(A_70, B_71), C_72)=k5_xboole_0(A_70, k5_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.50  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.50  tff(c_861, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k5_xboole_0(B_86, k5_xboole_0(A_85, B_86)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_397, c_14])).
% 3.18/1.50  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.50  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.50  tff(c_180, plain, (![A_64, B_65]: (k5_xboole_0(k5_xboole_0(A_64, B_65), k2_xboole_0(A_64, B_65))=k3_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.18/1.50  tff(c_213, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_13, A_13))=k3_xboole_0(A_13, A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_180])).
% 3.18/1.50  tff(c_221, plain, (![A_13]: (k5_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_213])).
% 3.18/1.50  tff(c_485, plain, (![A_13, C_72]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_72))=k5_xboole_0(k1_xboole_0, C_72))), inference(superposition, [status(thm), theory('equality')], [c_14, c_397])).
% 3.18/1.50  tff(c_502, plain, (![A_13, C_72]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_72))=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_221, c_485])).
% 3.18/1.50  tff(c_869, plain, (![B_86, A_85]: (k5_xboole_0(B_86, k5_xboole_0(A_85, B_86))=k5_xboole_0(A_85, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_861, c_502])).
% 3.18/1.50  tff(c_1007, plain, (![B_87, A_88]: (k5_xboole_0(B_87, k5_xboole_0(A_88, B_87))=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_869])).
% 3.18/1.50  tff(c_976, plain, (![B_86, A_85]: (k5_xboole_0(B_86, k5_xboole_0(A_85, B_86))=A_85)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_869])).
% 3.18/1.50  tff(c_1010, plain, (![A_88, B_87]: (k5_xboole_0(k5_xboole_0(A_88, B_87), A_88)=B_87)), inference(superposition, [status(thm), theory('equality')], [c_1007, c_976])).
% 3.18/1.50  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.50  tff(c_135, plain, (![A_59, B_60]: (k2_xboole_0(A_59, B_60)=B_60 | ~r1_tarski(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.18/1.50  tff(c_142, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_135])).
% 3.18/1.50  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.50  tff(c_147, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_142, c_2])).
% 3.18/1.50  tff(c_195, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_147, c_180])).
% 3.18/1.50  tff(c_1348, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1010, c_195])).
% 3.18/1.50  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.50  tff(c_143, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_135])).
% 3.18/1.50  tff(c_198, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_143, c_180])).
% 3.18/1.50  tff(c_12, plain, (![A_10, B_11, C_12]: (k5_xboole_0(k5_xboole_0(A_10, B_11), C_12)=k5_xboole_0(A_10, k5_xboole_0(B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.50  tff(c_589, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_198, c_12])).
% 3.18/1.50  tff(c_598, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_589])).
% 3.18/1.50  tff(c_32, plain, (![A_45, C_47, B_46, D_48]: (k3_xboole_0(k2_zfmisc_1(A_45, C_47), k2_zfmisc_1(B_46, D_48))=k2_zfmisc_1(k3_xboole_0(A_45, B_46), k3_xboole_0(C_47, D_48)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.50  tff(c_34, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.50  tff(c_39, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.18/1.50  tff(c_603, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_598, c_39])).
% 3.18/1.50  tff(c_1351, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1348, c_603])).
% 3.18/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  Inference rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Ref     : 0
% 3.18/1.50  #Sup     : 342
% 3.18/1.50  #Fact    : 0
% 3.18/1.50  #Define  : 0
% 3.18/1.50  #Split   : 0
% 3.18/1.50  #Chain   : 0
% 3.18/1.50  #Close   : 0
% 3.18/1.50  
% 3.18/1.50  Ordering : KBO
% 3.18/1.50  
% 3.18/1.50  Simplification rules
% 3.18/1.50  ----------------------
% 3.18/1.50  #Subsume      : 1
% 3.18/1.50  #Demod        : 235
% 3.18/1.50  #Tautology    : 229
% 3.18/1.50  #SimpNegUnit  : 0
% 3.18/1.50  #BackRed      : 8
% 3.18/1.50  
% 3.18/1.50  #Partial instantiations: 0
% 3.18/1.50  #Strategies tried      : 1
% 3.18/1.50  
% 3.18/1.50  Timing (in seconds)
% 3.18/1.50  ----------------------
% 3.18/1.51  Preprocessing        : 0.32
% 3.18/1.51  Parsing              : 0.17
% 3.18/1.51  CNF conversion       : 0.02
% 3.18/1.51  Main loop            : 0.41
% 3.18/1.51  Inferencing          : 0.14
% 3.18/1.51  Reduction            : 0.17
% 3.18/1.51  Demodulation         : 0.13
% 3.18/1.51  BG Simplification    : 0.02
% 3.18/1.51  Subsumption          : 0.06
% 3.18/1.51  Abstraction          : 0.03
% 3.18/1.51  MUC search           : 0.00
% 3.18/1.51  Cooper               : 0.00
% 3.18/1.51  Total                : 0.77
% 3.18/1.51  Index Insertion      : 0.00
% 3.18/1.51  Index Deletion       : 0.00
% 3.18/1.51  Index Matching       : 0.00
% 3.18/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
