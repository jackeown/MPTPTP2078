%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 7.90s
% Output     : CNFRefutation 7.90s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 118 expanded)
%              Number of leaves         :   31 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   75 ( 127 expanded)
%              Number of equality atoms :   56 (  89 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    ! [A_23] : k2_subset_1(A_23) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_37,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_321,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_329,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_321])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_336,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_14])).

tff(c_305,plain,(
    ! [A_54,B_55] :
      ( k3_subset_1(A_54,k3_subset_1(A_54,B_55)) = B_55
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_308,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_305])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(k3_subset_1(A_26,B_27),k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_27,k1_zfmisc_1(A_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_15091,plain,(
    ! [A_227,B_228] :
      ( k4_xboole_0(A_227,k3_subset_1(A_227,B_228)) = k3_subset_1(A_227,k3_subset_1(A_227,B_228))
      | ~ m1_subset_1(B_228,k1_zfmisc_1(A_227)) ) ),
    inference(resolution,[status(thm)],[c_28,c_321])).

tff(c_15095,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_15091])).

tff(c_15098,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_308,c_15095])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k3_xboole_0(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_177])).

tff(c_195,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_192])).

tff(c_627,plain,(
    ! [A_69,B_70,C_71] : k3_xboole_0(k4_xboole_0(A_69,B_70),k4_xboole_0(A_69,C_71)) = k4_xboole_0(A_69,k2_xboole_0(B_70,C_71)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_695,plain,(
    ! [A_7,B_70] : k4_xboole_0(A_7,k2_xboole_0(B_70,k1_xboole_0)) = k3_xboole_0(k4_xboole_0(A_7,B_70),A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_627])).

tff(c_887,plain,(
    ! [A_77,B_78] : k3_xboole_0(k4_xboole_0(A_77,B_78),A_77) = k4_xboole_0(A_77,B_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_695])).

tff(c_924,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(k3_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_887])).

tff(c_943,plain,(
    ! [A_11,B_12] : k3_xboole_0(k3_xboole_0(A_11,B_12),A_11) = k3_xboole_0(A_11,B_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_924])).

tff(c_72,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_88,plain,(
    ! [A_38] : k2_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_4])).

tff(c_692,plain,(
    ! [A_7,C_71] : k4_xboole_0(A_7,k2_xboole_0(k1_xboole_0,C_71)) = k3_xboole_0(A_7,k4_xboole_0(A_7,C_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_627])).

tff(c_710,plain,(
    ! [A_7,C_71] : k3_xboole_0(A_7,k4_xboole_0(A_7,C_71)) = k4_xboole_0(A_7,C_71) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_692])).

tff(c_186,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,k4_xboole_0(A_11,B_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_177])).

tff(c_1383,plain,(
    ! [A_93,B_94] : k4_xboole_0(A_93,k3_xboole_0(A_93,B_94)) = k4_xboole_0(A_93,B_94) ),
    inference(demodulation,[status(thm),theory(equality)],[c_710,c_186])).

tff(c_1434,plain,(
    ! [A_11,B_12] : k4_xboole_0(k3_xboole_0(A_11,B_12),k3_xboole_0(A_11,B_12)) = k4_xboole_0(k3_xboole_0(A_11,B_12),A_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_943,c_1383])).

tff(c_1502,plain,(
    ! [A_95,B_96] : k4_xboole_0(k3_xboole_0(A_95,B_96),A_95) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_1434])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1525,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = k2_xboole_0(A_95,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1502,c_8])).

tff(c_1582,plain,(
    ! [A_95,B_96] : k2_xboole_0(A_95,k3_xboole_0(A_95,B_96)) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1525])).

tff(c_15157,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_15098,c_1582])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_329,c_8])).

tff(c_339,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_333])).

tff(c_15355,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15157,c_339])).

tff(c_1010,plain,(
    ! [A_81,B_82,C_83] :
      ( k4_subset_1(A_81,B_82,C_83) = k2_xboole_0(B_82,C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(A_81))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_17073,plain,(
    ! [A_236,B_237,B_238] :
      ( k4_subset_1(A_236,B_237,k3_subset_1(A_236,B_238)) = k2_xboole_0(B_237,k3_subset_1(A_236,B_238))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(A_236))
      | ~ m1_subset_1(B_238,k1_zfmisc_1(A_236)) ) ),
    inference(resolution,[status(thm)],[c_28,c_1010])).

tff(c_17216,plain,(
    ! [B_239] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_239)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_239))
      | ~ m1_subset_1(B_239,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_36,c_17073])).

tff(c_17223,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_17216])).

tff(c_17226,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15355,c_17223])).

tff(c_17228,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_17226])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:21:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.90/3.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/3.09  
% 7.90/3.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/3.09  %$ m1_subset_1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.90/3.09  
% 7.90/3.09  %Foreground sorts:
% 7.90/3.09  
% 7.90/3.09  
% 7.90/3.09  %Background operators:
% 7.90/3.09  
% 7.90/3.09  
% 7.90/3.09  %Foreground operators:
% 7.90/3.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.90/3.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.90/3.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.90/3.09  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.90/3.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.90/3.09  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.90/3.09  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 7.90/3.09  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.90/3.09  tff('#skF_2', type, '#skF_2': $i).
% 7.90/3.09  tff('#skF_1', type, '#skF_1': $i).
% 7.90/3.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.90/3.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.90/3.09  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.90/3.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.90/3.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.90/3.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.90/3.09  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.90/3.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.90/3.09  
% 7.90/3.10  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 7.90/3.10  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 7.90/3.10  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 7.90/3.10  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.90/3.10  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.90/3.10  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 7.90/3.10  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 7.90/3.10  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 7.90/3.10  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 7.90/3.10  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_xboole_1)).
% 7.90/3.10  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 7.90/3.10  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.90/3.10  tff(f_67, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 7.90/3.10  tff(c_24, plain, (![A_23]: (k2_subset_1(A_23)=A_23)), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.90/3.10  tff(c_34, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.90/3.10  tff(c_37, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_34])).
% 7.90/3.10  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.90/3.10  tff(c_321, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.90/3.10  tff(c_329, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_321])).
% 7.90/3.10  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/3.10  tff(c_336, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_329, c_14])).
% 7.90/3.10  tff(c_305, plain, (![A_54, B_55]: (k3_subset_1(A_54, k3_subset_1(A_54, B_55))=B_55 | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 7.90/3.10  tff(c_308, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_36, c_305])).
% 7.90/3.10  tff(c_28, plain, (![A_26, B_27]: (m1_subset_1(k3_subset_1(A_26, B_27), k1_zfmisc_1(A_26)) | ~m1_subset_1(B_27, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.90/3.10  tff(c_15091, plain, (![A_227, B_228]: (k4_xboole_0(A_227, k3_subset_1(A_227, B_228))=k3_subset_1(A_227, k3_subset_1(A_227, B_228)) | ~m1_subset_1(B_228, k1_zfmisc_1(A_227)))), inference(resolution, [status(thm)], [c_28, c_321])).
% 7.90/3.10  tff(c_15095, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_15091])).
% 7.90/3.10  tff(c_15098, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_308, c_15095])).
% 7.90/3.10  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.90/3.10  tff(c_6, plain, (![A_4]: (k3_xboole_0(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.90/3.10  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.90/3.10  tff(c_177, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.90/3.10  tff(c_192, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_177])).
% 7.90/3.10  tff(c_195, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_192])).
% 7.90/3.10  tff(c_627, plain, (![A_69, B_70, C_71]: (k3_xboole_0(k4_xboole_0(A_69, B_70), k4_xboole_0(A_69, C_71))=k4_xboole_0(A_69, k2_xboole_0(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.90/3.10  tff(c_695, plain, (![A_7, B_70]: (k4_xboole_0(A_7, k2_xboole_0(B_70, k1_xboole_0))=k3_xboole_0(k4_xboole_0(A_7, B_70), A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_627])).
% 7.90/3.10  tff(c_887, plain, (![A_77, B_78]: (k3_xboole_0(k4_xboole_0(A_77, B_78), A_77)=k4_xboole_0(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_695])).
% 7.90/3.10  tff(c_924, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_14, c_887])).
% 7.90/3.10  tff(c_943, plain, (![A_11, B_12]: (k3_xboole_0(k3_xboole_0(A_11, B_12), A_11)=k3_xboole_0(A_11, B_12))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_924])).
% 7.90/3.10  tff(c_72, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.90/3.10  tff(c_88, plain, (![A_38]: (k2_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_72, c_4])).
% 7.90/3.10  tff(c_692, plain, (![A_7, C_71]: (k4_xboole_0(A_7, k2_xboole_0(k1_xboole_0, C_71))=k3_xboole_0(A_7, k4_xboole_0(A_7, C_71)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_627])).
% 7.90/3.10  tff(c_710, plain, (![A_7, C_71]: (k3_xboole_0(A_7, k4_xboole_0(A_7, C_71))=k4_xboole_0(A_7, C_71))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_692])).
% 7.90/3.10  tff(c_186, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k3_xboole_0(A_11, k4_xboole_0(A_11, B_12)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_177])).
% 7.90/3.10  tff(c_1383, plain, (![A_93, B_94]: (k4_xboole_0(A_93, k3_xboole_0(A_93, B_94))=k4_xboole_0(A_93, B_94))), inference(demodulation, [status(thm), theory('equality')], [c_710, c_186])).
% 7.90/3.10  tff(c_1434, plain, (![A_11, B_12]: (k4_xboole_0(k3_xboole_0(A_11, B_12), k3_xboole_0(A_11, B_12))=k4_xboole_0(k3_xboole_0(A_11, B_12), A_11))), inference(superposition, [status(thm), theory('equality')], [c_943, c_1383])).
% 7.90/3.10  tff(c_1502, plain, (![A_95, B_96]: (k4_xboole_0(k3_xboole_0(A_95, B_96), A_95)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_1434])).
% 7.90/3.10  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.90/3.10  tff(c_1525, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k3_xboole_0(A_95, B_96))=k2_xboole_0(A_95, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1502, c_8])).
% 7.90/3.10  tff(c_1582, plain, (![A_95, B_96]: (k2_xboole_0(A_95, k3_xboole_0(A_95, B_96))=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_1525])).
% 7.90/3.10  tff(c_15157, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_15098, c_1582])).
% 7.90/3.10  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.90/3.10  tff(c_333, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_329, c_8])).
% 7.90/3.10  tff(c_339, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_333])).
% 7.90/3.10  tff(c_15355, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15157, c_339])).
% 7.90/3.10  tff(c_1010, plain, (![A_81, B_82, C_83]: (k4_subset_1(A_81, B_82, C_83)=k2_xboole_0(B_82, C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(A_81)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 7.90/3.10  tff(c_17073, plain, (![A_236, B_237, B_238]: (k4_subset_1(A_236, B_237, k3_subset_1(A_236, B_238))=k2_xboole_0(B_237, k3_subset_1(A_236, B_238)) | ~m1_subset_1(B_237, k1_zfmisc_1(A_236)) | ~m1_subset_1(B_238, k1_zfmisc_1(A_236)))), inference(resolution, [status(thm)], [c_28, c_1010])).
% 7.90/3.10  tff(c_17216, plain, (![B_239]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_239))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_239)) | ~m1_subset_1(B_239, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_36, c_17073])).
% 7.90/3.10  tff(c_17223, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_17216])).
% 7.90/3.10  tff(c_17226, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15355, c_17223])).
% 7.90/3.10  tff(c_17228, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_17226])).
% 7.90/3.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.90/3.10  
% 7.90/3.10  Inference rules
% 7.90/3.10  ----------------------
% 7.90/3.10  #Ref     : 0
% 7.90/3.10  #Sup     : 4311
% 7.90/3.10  #Fact    : 0
% 7.90/3.10  #Define  : 0
% 7.90/3.10  #Split   : 0
% 7.90/3.10  #Chain   : 0
% 7.90/3.10  #Close   : 0
% 7.90/3.10  
% 7.90/3.10  Ordering : KBO
% 7.90/3.10  
% 7.90/3.11  Simplification rules
% 7.90/3.11  ----------------------
% 7.90/3.11  #Subsume      : 4
% 7.90/3.11  #Demod        : 4782
% 7.90/3.11  #Tautology    : 2868
% 7.90/3.11  #SimpNegUnit  : 1
% 7.90/3.11  #BackRed      : 8
% 7.90/3.11  
% 7.90/3.11  #Partial instantiations: 0
% 7.90/3.11  #Strategies tried      : 1
% 7.90/3.11  
% 7.90/3.11  Timing (in seconds)
% 7.90/3.11  ----------------------
% 7.90/3.11  Preprocessing        : 0.30
% 7.90/3.11  Parsing              : 0.16
% 7.90/3.11  CNF conversion       : 0.02
% 7.90/3.11  Main loop            : 2.00
% 7.90/3.11  Inferencing          : 0.45
% 7.90/3.11  Reduction            : 1.12
% 7.90/3.11  Demodulation         : 0.99
% 7.90/3.11  BG Simplification    : 0.06
% 7.90/3.11  Subsumption          : 0.27
% 7.90/3.11  Abstraction          : 0.09
% 7.90/3.11  MUC search           : 0.00
% 7.90/3.11  Cooper               : 0.00
% 7.90/3.11  Total                : 2.34
% 7.90/3.11  Index Insertion      : 0.00
% 7.90/3.11  Index Deletion       : 0.00
% 7.90/3.11  Index Matching       : 0.00
% 7.90/3.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
