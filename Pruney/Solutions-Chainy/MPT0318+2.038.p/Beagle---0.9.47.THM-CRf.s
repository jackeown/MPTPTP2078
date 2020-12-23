%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:06 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   56 (  85 expanded)
%              Number of leaves         :   28 (  41 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 111 expanded)
%              Number of equality atoms :   46 ( 109 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_34,plain,(
    ! [B_43] : k2_zfmisc_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_131,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_146,plain,(
    ! [B_58,A_59] :
      ( k1_xboole_0 = B_58
      | k1_xboole_0 = A_59
      | k2_zfmisc_1(A_59,B_58) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_149,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_146])).

tff(c_158,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_149])).

tff(c_36,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(B_45),k1_tarski(B_45)) != k1_tarski(B_45) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_168,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_36])).

tff(c_177,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_158,c_168])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_69,B_70] : k5_xboole_0(k5_xboole_0(A_69,B_70),k2_xboole_0(A_69,B_70)) = k3_xboole_0(A_69,B_70) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_273,plain,(
    ! [A_1] : k5_xboole_0(k5_xboole_0(A_1,A_1),A_1) = k3_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_284,plain,(
    ! [A_71] : k5_xboole_0(k1_xboole_0,A_71) = k3_xboole_0(A_71,A_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_273])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_300,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_6])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_394,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_4])).

tff(c_397,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_394])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_397])).

tff(c_400,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_425,plain,(
    ! [B_80,A_81] :
      ( k1_xboole_0 = B_80
      | k1_xboole_0 = A_81
      | k2_zfmisc_1(A_81,B_80) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_428,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_425])).

tff(c_437,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_428])).

tff(c_401,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_442,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_401])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:47:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.28  
% 2.08/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.29  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.29  
% 2.08/1.29  %Foreground sorts:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Background operators:
% 2.08/1.29  
% 2.08/1.29  
% 2.08/1.29  %Foreground operators:
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.08/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.08/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.08/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.08/1.29  
% 2.08/1.30  tff(f_59, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.08/1.30  tff(f_74, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.08/1.30  tff(f_64, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.08/1.30  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.08/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.08/1.30  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.08/1.30  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.08/1.30  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.08/1.30  tff(c_34, plain, (![B_43]: (k2_zfmisc_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.30  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.30  tff(c_40, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.08/1.30  tff(c_131, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_40])).
% 2.08/1.30  tff(c_146, plain, (![B_58, A_59]: (k1_xboole_0=B_58 | k1_xboole_0=A_59 | k2_zfmisc_1(A_59, B_58)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.30  tff(c_149, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_131, c_146])).
% 2.08/1.30  tff(c_158, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_149])).
% 2.08/1.30  tff(c_36, plain, (![B_45]: (k4_xboole_0(k1_tarski(B_45), k1_tarski(B_45))!=k1_tarski(B_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.08/1.30  tff(c_168, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_158, c_36])).
% 2.08/1.30  tff(c_177, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_158, c_158, c_168])).
% 2.08/1.30  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.08/1.30  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.30  tff(c_255, plain, (![A_69, B_70]: (k5_xboole_0(k5_xboole_0(A_69, B_70), k2_xboole_0(A_69, B_70))=k3_xboole_0(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.30  tff(c_273, plain, (![A_1]: (k5_xboole_0(k5_xboole_0(A_1, A_1), A_1)=k3_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_255])).
% 2.08/1.30  tff(c_284, plain, (![A_71]: (k5_xboole_0(k1_xboole_0, A_71)=k3_xboole_0(A_71, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_273])).
% 2.08/1.30  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.08/1.30  tff(c_300, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_284, c_6])).
% 2.08/1.30  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.08/1.30  tff(c_394, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_300, c_4])).
% 2.08/1.30  tff(c_397, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_394])).
% 2.08/1.30  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_397])).
% 2.08/1.30  tff(c_400, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.08/1.30  tff(c_425, plain, (![B_80, A_81]: (k1_xboole_0=B_80 | k1_xboole_0=A_81 | k2_zfmisc_1(A_81, B_80)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.30  tff(c_428, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_400, c_425])).
% 2.08/1.30  tff(c_437, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_42, c_428])).
% 2.08/1.30  tff(c_401, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_40])).
% 2.08/1.30  tff(c_442, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_437, c_401])).
% 2.08/1.30  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_442])).
% 2.08/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  Inference rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Ref     : 0
% 2.08/1.30  #Sup     : 98
% 2.08/1.30  #Fact    : 0
% 2.08/1.30  #Define  : 0
% 2.08/1.30  #Split   : 1
% 2.08/1.30  #Chain   : 0
% 2.08/1.30  #Close   : 0
% 2.08/1.30  
% 2.08/1.30  Ordering : KBO
% 2.08/1.30  
% 2.08/1.30  Simplification rules
% 2.08/1.30  ----------------------
% 2.08/1.30  #Subsume      : 1
% 2.08/1.30  #Demod        : 23
% 2.08/1.30  #Tautology    : 65
% 2.08/1.30  #SimpNegUnit  : 5
% 2.08/1.30  #BackRed      : 3
% 2.08/1.30  
% 2.08/1.30  #Partial instantiations: 0
% 2.08/1.30  #Strategies tried      : 1
% 2.08/1.30  
% 2.08/1.30  Timing (in seconds)
% 2.08/1.30  ----------------------
% 2.08/1.30  Preprocessing        : 0.31
% 2.08/1.30  Parsing              : 0.16
% 2.08/1.30  CNF conversion       : 0.02
% 2.08/1.30  Main loop            : 0.20
% 2.08/1.30  Inferencing          : 0.07
% 2.08/1.30  Reduction            : 0.07
% 2.08/1.30  Demodulation         : 0.05
% 2.08/1.30  BG Simplification    : 0.02
% 2.08/1.30  Subsumption          : 0.03
% 2.08/1.30  Abstraction          : 0.01
% 2.08/1.30  MUC search           : 0.00
% 2.08/1.30  Cooper               : 0.00
% 2.08/1.30  Total                : 0.54
% 2.08/1.30  Index Insertion      : 0.00
% 2.08/1.30  Index Deletion       : 0.00
% 2.08/1.30  Index Matching       : 0.00
% 2.08/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
