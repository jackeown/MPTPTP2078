%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:53 EST 2020

% Result     : Theorem 2.93s
% Output     : CNFRefutation 2.93s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 222 expanded)
%              Number of leaves         :   31 (  93 expanded)
%              Depth                    :   13
%              Number of atoms          :   58 ( 227 expanded)
%              Number of equality atoms :   51 ( 194 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => k3_xboole_0(k2_zfmisc_1(A,D),k2_zfmisc_1(B,C)) = k2_zfmisc_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_276,plain,(
    ! [A_65,B_66] : k5_xboole_0(k5_xboole_0(A_65,B_66),k2_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_309,plain,(
    ! [A_5] : k5_xboole_0(A_5,k2_xboole_0(A_5,k1_xboole_0)) = k3_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_276])).

tff(c_317,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6,c_309])).

tff(c_423,plain,(
    ! [A_70,B_71,C_72] : k5_xboole_0(k5_xboole_0(A_70,B_71),C_72) = k5_xboole_0(A_70,k5_xboole_0(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_34,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_120,plain,(
    ! [A_55,B_56] :
      ( k2_xboole_0(A_55,B_56) = B_56
      | ~ r1_tarski(A_55,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_127,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_120])).

tff(c_306,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_276])).

tff(c_439,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_306])).

tff(c_514,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_317,c_439])).

tff(c_14,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [A_53,B_54] : k3_tarski(k2_tarski(A_53,B_54)) = k2_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_137,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(B_58,A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_105])).

tff(c_28,plain,(
    ! [A_40,B_41] : k3_tarski(k2_tarski(A_40,B_41)) = k2_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_160,plain,(
    ! [B_59,A_60] : k2_xboole_0(B_59,A_60) = k2_xboole_0(A_60,B_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_28])).

tff(c_175,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_160,c_127])).

tff(c_294,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),'#skF_4') = k3_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_276])).

tff(c_523,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_306])).

tff(c_729,plain,(
    ! [A_86,C_87] : k5_xboole_0(A_86,k5_xboole_0(A_86,C_87)) = k5_xboole_0(k1_xboole_0,C_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_423])).

tff(c_795,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = k5_xboole_0(A_5,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_729])).

tff(c_816,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_795])).

tff(c_493,plain,(
    ! [A_5,C_72] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_72)) = k5_xboole_0(k1_xboole_0,C_72) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_423])).

tff(c_893,plain,(
    ! [A_90,C_91] : k5_xboole_0(A_90,k5_xboole_0(A_90,C_91)) = C_91 ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_493])).

tff(c_936,plain,(
    k5_xboole_0(k5_xboole_0('#skF_3','#skF_4'),'#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_893])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] : k5_xboole_0(k5_xboole_0(A_6,B_7),C_8) = k5_xboole_0(A_6,k5_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1008,plain,(
    k5_xboole_0('#skF_3',k5_xboole_0('#skF_4','#skF_3')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_936,c_10])).

tff(c_818,plain,(
    ! [A_5,C_72] : k5_xboole_0(A_5,k5_xboole_0(A_5,C_72)) = C_72 ),
    inference(demodulation,[status(thm),theory(equality)],[c_816,c_493])).

tff(c_1044,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k5_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1008,c_818])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(k5_xboole_0(A_9,B_10),k2_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1170,plain,(
    k5_xboole_0(k5_xboole_0('#skF_4','#skF_3'),k2_xboole_0('#skF_3','#skF_4')) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1044,c_12])).

tff(c_1175,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_514,c_294,c_127,c_1170])).

tff(c_36,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_128,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_120])).

tff(c_303,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_128,c_276])).

tff(c_442,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_303])).

tff(c_515,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_317,c_442])).

tff(c_30,plain,(
    ! [A_42,C_44,B_43,D_45] : k3_xboole_0(k2_zfmisc_1(A_42,C_44),k2_zfmisc_1(B_43,D_45)) = k2_zfmisc_1(k3_xboole_0(A_42,B_43),k3_xboole_0(C_44,D_45)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_32,plain,(
    k3_xboole_0(k2_zfmisc_1('#skF_1','#skF_4'),k2_zfmisc_1('#skF_2','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_37,plain,(
    k2_zfmisc_1(k3_xboole_0('#skF_1','#skF_2'),k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_32])).

tff(c_538,plain,(
    k2_zfmisc_1('#skF_1',k3_xboole_0('#skF_4','#skF_3')) != k2_zfmisc_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_515,c_37])).

tff(c_1180,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1175,c_538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:04:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.93/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.49  
% 2.93/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.49  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.93/1.49  
% 2.93/1.49  %Foreground sorts:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Background operators:
% 2.93/1.49  
% 2.93/1.49  
% 2.93/1.49  %Foreground operators:
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.93/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.93/1.49  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.93/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.93/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.93/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.93/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.93/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.93/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.93/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.93/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.93/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.93/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.93/1.49  tff('#skF_4', type, '#skF_4': $i).
% 2.93/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.93/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.93/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.93/1.49  
% 2.93/1.50  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.93/1.50  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.93/1.50  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.93/1.50  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.93/1.50  tff(f_37, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.93/1.50  tff(f_64, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => (k3_xboole_0(k2_zfmisc_1(A, D), k2_zfmisc_1(B, C)) = k2_zfmisc_1(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_zfmisc_1)).
% 2.93/1.50  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.93/1.50  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.93/1.50  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.93/1.50  tff(f_57, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 2.93/1.50  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.93/1.50  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.93/1.50  tff(c_6, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.93/1.50  tff(c_276, plain, (![A_65, B_66]: (k5_xboole_0(k5_xboole_0(A_65, B_66), k2_xboole_0(A_65, B_66))=k3_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.50  tff(c_309, plain, (![A_5]: (k5_xboole_0(A_5, k2_xboole_0(A_5, k1_xboole_0))=k3_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_276])).
% 2.93/1.50  tff(c_317, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6, c_309])).
% 2.93/1.50  tff(c_423, plain, (![A_70, B_71, C_72]: (k5_xboole_0(k5_xboole_0(A_70, B_71), C_72)=k5_xboole_0(A_70, k5_xboole_0(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_34, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.93/1.50  tff(c_120, plain, (![A_55, B_56]: (k2_xboole_0(A_55, B_56)=B_56 | ~r1_tarski(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.93/1.50  tff(c_127, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_34, c_120])).
% 2.93/1.50  tff(c_306, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_127, c_276])).
% 2.93/1.50  tff(c_439, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_423, c_306])).
% 2.93/1.50  tff(c_514, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_317, c_439])).
% 2.93/1.50  tff(c_14, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.93/1.50  tff(c_105, plain, (![A_53, B_54]: (k3_tarski(k2_tarski(A_53, B_54))=k2_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.50  tff(c_137, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(B_58, A_57))), inference(superposition, [status(thm), theory('equality')], [c_14, c_105])).
% 2.93/1.50  tff(c_28, plain, (![A_40, B_41]: (k3_tarski(k2_tarski(A_40, B_41))=k2_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.93/1.50  tff(c_160, plain, (![B_59, A_60]: (k2_xboole_0(B_59, A_60)=k2_xboole_0(A_60, B_59))), inference(superposition, [status(thm), theory('equality')], [c_137, c_28])).
% 2.93/1.50  tff(c_175, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_160, c_127])).
% 2.93/1.50  tff(c_294, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_276])).
% 2.93/1.50  tff(c_523, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_306])).
% 2.93/1.50  tff(c_729, plain, (![A_86, C_87]: (k5_xboole_0(A_86, k5_xboole_0(A_86, C_87))=k5_xboole_0(k1_xboole_0, C_87))), inference(superposition, [status(thm), theory('equality')], [c_317, c_423])).
% 2.93/1.50  tff(c_795, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=k5_xboole_0(A_5, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_317, c_729])).
% 2.93/1.50  tff(c_816, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_795])).
% 2.93/1.50  tff(c_493, plain, (![A_5, C_72]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_72))=k5_xboole_0(k1_xboole_0, C_72))), inference(superposition, [status(thm), theory('equality')], [c_317, c_423])).
% 2.93/1.50  tff(c_893, plain, (![A_90, C_91]: (k5_xboole_0(A_90, k5_xboole_0(A_90, C_91))=C_91)), inference(demodulation, [status(thm), theory('equality')], [c_816, c_493])).
% 2.93/1.50  tff(c_936, plain, (k5_xboole_0(k5_xboole_0('#skF_3', '#skF_4'), '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_523, c_893])).
% 2.93/1.50  tff(c_10, plain, (![A_6, B_7, C_8]: (k5_xboole_0(k5_xboole_0(A_6, B_7), C_8)=k5_xboole_0(A_6, k5_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.93/1.50  tff(c_1008, plain, (k5_xboole_0('#skF_3', k5_xboole_0('#skF_4', '#skF_3'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_936, c_10])).
% 2.93/1.50  tff(c_818, plain, (![A_5, C_72]: (k5_xboole_0(A_5, k5_xboole_0(A_5, C_72))=C_72)), inference(demodulation, [status(thm), theory('equality')], [c_816, c_493])).
% 2.93/1.50  tff(c_1044, plain, (k5_xboole_0('#skF_3', '#skF_4')=k5_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1008, c_818])).
% 2.93/1.50  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(k5_xboole_0(A_9, B_10), k2_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.93/1.50  tff(c_1170, plain, (k5_xboole_0(k5_xboole_0('#skF_4', '#skF_3'), k2_xboole_0('#skF_3', '#skF_4'))=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1044, c_12])).
% 2.93/1.50  tff(c_1175, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_514, c_294, c_127, c_1170])).
% 2.93/1.50  tff(c_36, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.93/1.50  tff(c_128, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_36, c_120])).
% 2.93/1.50  tff(c_303, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_128, c_276])).
% 2.93/1.50  tff(c_442, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_423, c_303])).
% 2.93/1.50  tff(c_515, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8, c_317, c_442])).
% 2.93/1.50  tff(c_30, plain, (![A_42, C_44, B_43, D_45]: (k3_xboole_0(k2_zfmisc_1(A_42, C_44), k2_zfmisc_1(B_43, D_45))=k2_zfmisc_1(k3_xboole_0(A_42, B_43), k3_xboole_0(C_44, D_45)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.93/1.50  tff(c_32, plain, (k3_xboole_0(k2_zfmisc_1('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_2', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.93/1.50  tff(c_37, plain, (k2_zfmisc_1(k3_xboole_0('#skF_1', '#skF_2'), k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_32])).
% 2.93/1.50  tff(c_538, plain, (k2_zfmisc_1('#skF_1', k3_xboole_0('#skF_4', '#skF_3'))!=k2_zfmisc_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_515, c_37])).
% 2.93/1.50  tff(c_1180, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1175, c_538])).
% 2.93/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.93/1.50  
% 2.93/1.50  Inference rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Ref     : 0
% 2.93/1.50  #Sup     : 292
% 2.93/1.50  #Fact    : 0
% 2.93/1.50  #Define  : 0
% 2.93/1.50  #Split   : 0
% 2.93/1.50  #Chain   : 0
% 2.93/1.50  #Close   : 0
% 2.93/1.50  
% 2.93/1.50  Ordering : KBO
% 2.93/1.50  
% 2.93/1.50  Simplification rules
% 2.93/1.50  ----------------------
% 2.93/1.50  #Subsume      : 3
% 2.93/1.50  #Demod        : 200
% 2.93/1.50  #Tautology    : 197
% 2.93/1.50  #SimpNegUnit  : 0
% 2.93/1.50  #BackRed      : 13
% 2.93/1.50  
% 2.93/1.50  #Partial instantiations: 0
% 2.93/1.50  #Strategies tried      : 1
% 2.93/1.50  
% 2.93/1.50  Timing (in seconds)
% 2.93/1.50  ----------------------
% 2.93/1.51  Preprocessing        : 0.32
% 2.93/1.51  Parsing              : 0.18
% 2.93/1.51  CNF conversion       : 0.02
% 2.93/1.51  Main loop            : 0.37
% 2.93/1.51  Inferencing          : 0.13
% 2.93/1.51  Reduction            : 0.15
% 2.93/1.51  Demodulation         : 0.12
% 2.93/1.51  BG Simplification    : 0.02
% 2.93/1.51  Subsumption          : 0.05
% 2.93/1.51  Abstraction          : 0.02
% 2.93/1.51  MUC search           : 0.00
% 2.93/1.51  Cooper               : 0.00
% 2.93/1.51  Total                : 0.73
% 2.93/1.51  Index Insertion      : 0.00
% 2.93/1.51  Index Deletion       : 0.00
% 2.93/1.51  Index Matching       : 0.00
% 2.93/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
