%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:53 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.66s
% Verified   : 
% Statistics : Number of formulae       :   63 (  90 expanded)
%              Number of leaves         :   30 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   47 (  80 expanded)
%              Number of equality atoms :   40 (  67 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [B_50,A_51] : k5_xboole_0(B_50,A_51) = k5_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_133,plain,(
    ! [A_51] : k5_xboole_0(k1_xboole_0,A_51) = A_51 ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_10])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_582,plain,(
    ! [A_72,B_73,C_74] : k5_xboole_0(k5_xboole_0(A_72,B_73),C_74) = k5_xboole_0(A_72,k5_xboole_0(B_73,C_74)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_693,plain,(
    ! [A_13,C_74] : k5_xboole_0(A_13,k5_xboole_0(A_13,C_74)) = k5_xboole_0(k1_xboole_0,C_74) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_582])).

tff(c_722,plain,(
    ! [A_75,C_76] : k5_xboole_0(A_75,k5_xboole_0(A_75,C_76)) = C_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_693])).

tff(c_780,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k5_xboole_0(A_1,B_2)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_722])).

tff(c_803,plain,(
    ! [B_77,A_78] : k5_xboole_0(B_77,k5_xboole_0(A_78,B_77)) = A_78 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_722])).

tff(c_833,plain,(
    ! [A_1,B_2] : k5_xboole_0(k5_xboole_0(A_1,B_2),A_1) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_803])).

tff(c_18,plain,(
    ! [B_17,A_16] : k2_tarski(B_17,A_16) = k2_tarski(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_214,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_255,plain,(
    ! [B_59,A_60] : k3_tarski(k2_tarski(B_59,A_60)) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_214])).

tff(c_30,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_287,plain,(
    ! [B_64,A_65] : k2_xboole_0(B_64,A_65) = k2_xboole_0(A_65,B_64) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_30])).

tff(c_36,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_229,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(A_55,B_56) = B_56
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_229])).

tff(c_302,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_236])).

tff(c_339,plain,(
    ! [A_66,B_67] : k5_xboole_0(k5_xboole_0(A_66,B_67),k2_xboole_0(A_66,B_67)) = k3_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_360,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_339])).

tff(c_1635,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_833,c_360])).

tff(c_38,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_237,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_229])).

tff(c_369,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_339])).

tff(c_599,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_582,c_369])).

tff(c_701,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_14,c_599])).

tff(c_32,plain,(
    ! [A_40,C_42,B_41,D_43] : k3_xboole_0(k2_zfmisc_1(A_40,C_42),k2_zfmisc_1(B_41,D_43)) = k2_zfmisc_1(k3_xboole_0(A_40,B_41),k3_xboole_0(C_42,D_43)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_39,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_715,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_39])).

tff(c_1638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1635,c_715])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:10:17 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.61  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.61  
% 3.21/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.61  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.21/1.61  
% 3.21/1.61  %Foreground sorts:
% 3.21/1.61  
% 3.21/1.61  
% 3.21/1.61  %Background operators:
% 3.21/1.61  
% 3.21/1.61  
% 3.21/1.61  %Foreground operators:
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.21/1.61  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.61  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.21/1.61  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.61  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.21/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.61  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.61  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.21/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.21/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.21/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.21/1.61  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.21/1.61  
% 3.66/1.63  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.66/1.63  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.66/1.63  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.66/1.63  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.66/1.63  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.66/1.63  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.66/1.63  tff(f_66, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 3.66/1.63  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.66/1.63  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.66/1.63  tff(f_59, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 3.66/1.63  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.63  tff(c_117, plain, (![B_50, A_51]: (k5_xboole_0(B_50, A_51)=k5_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.66/1.63  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.66/1.63  tff(c_133, plain, (![A_51]: (k5_xboole_0(k1_xboole_0, A_51)=A_51)), inference(superposition, [status(thm), theory('equality')], [c_117, c_10])).
% 3.66/1.63  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.66/1.63  tff(c_582, plain, (![A_72, B_73, C_74]: (k5_xboole_0(k5_xboole_0(A_72, B_73), C_74)=k5_xboole_0(A_72, k5_xboole_0(B_73, C_74)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.66/1.63  tff(c_693, plain, (![A_13, C_74]: (k5_xboole_0(A_13, k5_xboole_0(A_13, C_74))=k5_xboole_0(k1_xboole_0, C_74))), inference(superposition, [status(thm), theory('equality')], [c_14, c_582])).
% 3.66/1.63  tff(c_722, plain, (![A_75, C_76]: (k5_xboole_0(A_75, k5_xboole_0(A_75, C_76))=C_76)), inference(demodulation, [status(thm), theory('equality')], [c_133, c_693])).
% 3.66/1.63  tff(c_780, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k5_xboole_0(A_1, B_2))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_722])).
% 3.66/1.63  tff(c_803, plain, (![B_77, A_78]: (k5_xboole_0(B_77, k5_xboole_0(A_78, B_77))=A_78)), inference(superposition, [status(thm), theory('equality')], [c_2, c_722])).
% 3.66/1.63  tff(c_833, plain, (![A_1, B_2]: (k5_xboole_0(k5_xboole_0(A_1, B_2), A_1)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_780, c_803])).
% 3.66/1.63  tff(c_18, plain, (![B_17, A_16]: (k2_tarski(B_17, A_16)=k2_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.66/1.63  tff(c_214, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.66/1.63  tff(c_255, plain, (![B_59, A_60]: (k3_tarski(k2_tarski(B_59, A_60))=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_18, c_214])).
% 3.66/1.63  tff(c_30, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.66/1.63  tff(c_287, plain, (![B_64, A_65]: (k2_xboole_0(B_64, A_65)=k2_xboole_0(A_65, B_64))), inference(superposition, [status(thm), theory('equality')], [c_255, c_30])).
% 3.66/1.63  tff(c_36, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.63  tff(c_229, plain, (![A_55, B_56]: (k2_xboole_0(A_55, B_56)=B_56 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.66/1.63  tff(c_236, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_36, c_229])).
% 3.66/1.63  tff(c_302, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_287, c_236])).
% 3.66/1.63  tff(c_339, plain, (![A_66, B_67]: (k5_xboole_0(k5_xboole_0(A_66, B_67), k2_xboole_0(A_66, B_67))=k3_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.66/1.63  tff(c_360, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_302, c_339])).
% 3.66/1.63  tff(c_1635, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_833, c_360])).
% 3.66/1.63  tff(c_38, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.63  tff(c_237, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_38, c_229])).
% 3.66/1.63  tff(c_369, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_237, c_339])).
% 3.66/1.63  tff(c_599, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_582, c_369])).
% 3.66/1.63  tff(c_701, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_14, c_599])).
% 3.66/1.63  tff(c_32, plain, (![A_40, C_42, B_41, D_43]: (k3_xboole_0(k2_zfmisc_1(A_40, C_42), k2_zfmisc_1(B_41, D_43))=k2_zfmisc_1(k3_xboole_0(A_40, B_41), k3_xboole_0(C_42, D_43)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.66/1.63  tff(c_34, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.66/1.63  tff(c_39, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 3.66/1.63  tff(c_715, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_701, c_39])).
% 3.66/1.63  tff(c_1638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1635, c_715])).
% 3.66/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.66/1.63  
% 3.66/1.63  Inference rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Ref     : 0
% 3.66/1.63  #Sup     : 400
% 3.66/1.63  #Fact    : 0
% 3.66/1.63  #Define  : 0
% 3.66/1.63  #Split   : 0
% 3.66/1.63  #Chain   : 0
% 3.66/1.63  #Close   : 0
% 3.66/1.63  
% 3.66/1.63  Ordering : KBO
% 3.66/1.63  
% 3.66/1.63  Simplification rules
% 3.66/1.63  ----------------------
% 3.66/1.63  #Subsume      : 8
% 3.66/1.63  #Demod        : 224
% 3.66/1.63  #Tautology    : 254
% 3.66/1.63  #SimpNegUnit  : 0
% 3.66/1.63  #BackRed      : 4
% 3.66/1.63  
% 3.66/1.63  #Partial instantiations: 0
% 3.66/1.63  #Strategies tried      : 1
% 3.66/1.63  
% 3.66/1.63  Timing (in seconds)
% 3.66/1.63  ----------------------
% 3.66/1.63  Preprocessing        : 0.34
% 3.66/1.63  Parsing              : 0.18
% 3.66/1.63  CNF conversion       : 0.02
% 3.66/1.63  Main loop            : 0.48
% 3.66/1.63  Inferencing          : 0.16
% 3.66/1.63  Reduction            : 0.20
% 3.66/1.63  Demodulation         : 0.17
% 3.66/1.63  BG Simplification    : 0.02
% 3.66/1.63  Subsumption          : 0.07
% 3.66/1.63  Abstraction          : 0.03
% 3.66/1.63  MUC search           : 0.00
% 3.66/1.63  Cooper               : 0.00
% 3.66/1.63  Total                : 0.85
% 3.66/1.63  Index Insertion      : 0.00
% 3.66/1.63  Index Deletion       : 0.00
% 3.66/1.63  Index Matching       : 0.00
% 3.66/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
