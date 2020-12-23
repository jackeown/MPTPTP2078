%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:43 EST 2020

% Result     : Theorem 10.01s
% Output     : CNFRefutation 10.01s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 255 expanded)
%              Number of leaves         :   36 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  108 ( 412 expanded)
%              Number of equality atoms :   58 ( 180 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( ( r1_xboole_0(B,C)
                & r1_xboole_0(k3_subset_1(A,B),k3_subset_1(A,C)) )
             => B = k3_subset_1(A,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(c_44,plain,(
    k3_subset_1('#skF_1','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [A_47,B_48] :
      ( m1_subset_1(k3_subset_1(A_47,B_48),k1_zfmisc_1(A_47))
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_46,plain,(
    r1_xboole_0(k3_subset_1('#skF_1','#skF_2'),k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2798,plain,(
    ! [B_165,C_166,A_167] :
      ( r1_tarski(B_165,C_166)
      | ~ r1_xboole_0(B_165,k3_subset_1(A_167,C_166))
      | ~ m1_subset_1(C_166,k1_zfmisc_1(A_167))
      | ~ m1_subset_1(B_165,k1_zfmisc_1(A_167)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2821,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_2798])).

tff(c_2830,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2821])).

tff(c_5028,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2830])).

tff(c_5031,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_5028])).

tff(c_5035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_5031])).

tff(c_5036,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2830])).

tff(c_48,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,(
    ! [B_58,A_59] :
      ( r1_xboole_0(B_58,A_59)
      | ~ r1_xboole_0(A_59,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_48,c_69])).

tff(c_89,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = A_62
      | ~ r1_xboole_0(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_100,plain,(
    k4_xboole_0('#skF_3','#skF_2') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_72,c_89])).

tff(c_382,plain,(
    ! [A_83,B_84] :
      ( k3_subset_1(A_83,k3_subset_1(A_83,B_84)) = B_84
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_83)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_388,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_50,c_382])).

tff(c_556,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_564,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_556])).

tff(c_14,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_591,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_14])).

tff(c_794,plain,(
    ! [A_104,B_105] :
      ( m1_subset_1(k3_subset_1(A_104,B_105),k1_zfmisc_1(A_104))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_34,plain,(
    ! [A_45,B_46] :
      ( k4_xboole_0(A_45,B_46) = k3_subset_1(A_45,B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18176,plain,(
    ! [A_289,B_290] :
      ( k4_xboole_0(A_289,k3_subset_1(A_289,B_290)) = k3_subset_1(A_289,k3_subset_1(A_289,B_290))
      | ~ m1_subset_1(B_290,k1_zfmisc_1(A_289)) ) ),
    inference(resolution,[status(thm)],[c_794,c_34])).

tff(c_18184,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_18176])).

tff(c_18191,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_388,c_591,c_18184])).

tff(c_563,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_52,c_556])).

tff(c_429,plain,(
    ! [A_87,B_88,C_89] : k4_xboole_0(k4_xboole_0(A_87,B_88),C_89) = k4_xboole_0(A_87,k2_xboole_0(B_88,C_89)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_477,plain,(
    ! [A_12,B_13,C_89] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_89)) = k4_xboole_0(k3_xboole_0(A_12,B_13),C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_429])).

tff(c_1300,plain,(
    ! [A_118,B_119,C_120] : k3_xboole_0(k4_xboole_0(A_118,B_119),k4_xboole_0(A_118,C_120)) = k4_xboole_0(A_118,k2_xboole_0(B_119,C_120)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1413,plain,(
    ! [A_12,B_13,C_120] : k4_xboole_0(A_12,k2_xboole_0(k4_xboole_0(A_12,B_13),C_120)) = k3_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,C_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1300])).

tff(c_13341,plain,(
    ! [A_258,B_259,C_260] : k3_xboole_0(k3_xboole_0(A_258,B_259),k4_xboole_0(A_258,C_260)) = k4_xboole_0(k3_xboole_0(A_258,B_259),C_260) ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_1413])).

tff(c_13674,plain,(
    ! [B_259] : k3_xboole_0(k3_xboole_0('#skF_1',B_259),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0(k3_xboole_0('#skF_1',B_259),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_13341])).

tff(c_18205,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') = k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_18191,c_13674])).

tff(c_18249,plain,(
    k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_18191,c_18205])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    ! [A_70,B_71] : k4_xboole_0(k2_xboole_0(A_70,B_71),B_71) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_150,plain,(
    ! [A_70] : k4_xboole_0(A_70,k1_xboole_0) = k2_xboole_0(A_70,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_6])).

tff(c_159,plain,(
    ! [A_70] : k2_xboole_0(A_70,k1_xboole_0) = A_70 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_150])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k4_xboole_0(k4_xboole_0(A_7,B_8),C_9) = k4_xboole_0(A_7,k2_xboole_0(B_8,C_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_568,plain,(
    ! [C_9] : k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_9) = k4_xboole_0('#skF_1',k2_xboole_0('#skF_2',C_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_10])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [A_73,B_74] : k4_xboole_0(A_73,k4_xboole_0(A_73,B_74)) = k3_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_207,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k3_xboole_0(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_180])).

tff(c_210,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_207])).

tff(c_496,plain,(
    ! [A_4,C_89] : k4_xboole_0(A_4,k2_xboole_0(k1_xboole_0,C_89)) = k4_xboole_0(A_4,C_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_429])).

tff(c_1443,plain,(
    ! [A_4,C_120] : k4_xboole_0(A_4,k2_xboole_0(k1_xboole_0,C_120)) = k3_xboole_0(A_4,k4_xboole_0(A_4,C_120)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1300])).

tff(c_1472,plain,(
    ! [A_4,C_120] : k3_xboole_0(A_4,k4_xboole_0(A_4,C_120)) = k4_xboole_0(A_4,C_120) ),
    inference(demodulation,[status(thm),theory(equality)],[c_496,c_1443])).

tff(c_189,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,k4_xboole_0(A_12,B_13)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_180])).

tff(c_3444,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_189])).

tff(c_19219,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18249,c_3444])).

tff(c_19252,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_19219])).

tff(c_256,plain,(
    ! [A_77,B_78] :
      ( k2_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = B_78
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_5,B_6] : k4_xboole_0(k2_xboole_0(A_5,B_6),B_6) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_262,plain,(
    ! [B_78,A_77] :
      ( k4_xboole_0(B_78,k4_xboole_0(B_78,A_77)) = k4_xboole_0(A_77,k4_xboole_0(B_78,A_77))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_8])).

tff(c_288,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,k4_xboole_0(B_78,A_77)) = k3_xboole_0(B_78,A_77)
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_262])).

tff(c_20197,plain,
    ( k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_19252,c_288])).

tff(c_20265,plain,(
    k3_subset_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5036,c_18249,c_563,c_159,c_568,c_20197])).

tff(c_387,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_52,c_382])).

tff(c_20314,plain,(
    k3_subset_1('#skF_1','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20265,c_387])).

tff(c_20336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_20314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.01/4.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/4.05  
% 10.01/4.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/4.05  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.01/4.05  
% 10.01/4.05  %Foreground sorts:
% 10.01/4.05  
% 10.01/4.05  
% 10.01/4.05  %Background operators:
% 10.01/4.05  
% 10.01/4.05  
% 10.01/4.05  %Foreground operators:
% 10.01/4.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.01/4.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.01/4.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.01/4.05  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.01/4.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.01/4.05  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.01/4.05  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.01/4.05  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 10.01/4.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 10.01/4.05  tff('#skF_2', type, '#skF_2': $i).
% 10.01/4.05  tff('#skF_3', type, '#skF_3': $i).
% 10.01/4.05  tff('#skF_1', type, '#skF_1': $i).
% 10.01/4.05  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.01/4.05  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.01/4.05  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.01/4.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.01/4.05  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.01/4.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.01/4.05  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.01/4.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.01/4.05  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.01/4.05  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.01/4.05  
% 10.01/4.07  tff(f_94, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_xboole_0(B, C) & r1_xboole_0(k3_subset_1(A, B), k3_subset_1(A, C))) => (B = k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_subset_1)).
% 10.01/4.07  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 10.01/4.07  tff(f_82, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 10.01/4.07  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 10.01/4.07  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 10.01/4.07  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 10.01/4.07  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 10.01/4.07  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.01/4.07  tff(f_37, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 10.01/4.07  tff(f_45, axiom, (![A, B, C]: (k4_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_xboole_1)).
% 10.01/4.07  tff(f_33, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.01/4.07  tff(f_35, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 10.01/4.07  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.01/4.07  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 10.01/4.07  tff(c_44, plain, (k3_subset_1('#skF_1', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.01/4.07  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.01/4.07  tff(c_36, plain, (![A_47, B_48]: (m1_subset_1(k3_subset_1(A_47, B_48), k1_zfmisc_1(A_47)) | ~m1_subset_1(B_48, k1_zfmisc_1(A_47)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.01/4.07  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.01/4.07  tff(c_46, plain, (r1_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.01/4.07  tff(c_2798, plain, (![B_165, C_166, A_167]: (r1_tarski(B_165, C_166) | ~r1_xboole_0(B_165, k3_subset_1(A_167, C_166)) | ~m1_subset_1(C_166, k1_zfmisc_1(A_167)) | ~m1_subset_1(B_165, k1_zfmisc_1(A_167)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 10.01/4.07  tff(c_2821, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_46, c_2798])).
% 10.01/4.07  tff(c_2830, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2821])).
% 10.01/4.07  tff(c_5028, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2830])).
% 10.01/4.07  tff(c_5031, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_5028])).
% 10.01/4.07  tff(c_5035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_52, c_5031])).
% 10.01/4.07  tff(c_5036, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitRight, [status(thm)], [c_2830])).
% 10.01/4.07  tff(c_48, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.01/4.07  tff(c_69, plain, (![B_58, A_59]: (r1_xboole_0(B_58, A_59) | ~r1_xboole_0(A_59, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 10.01/4.07  tff(c_72, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_48, c_69])).
% 10.01/4.07  tff(c_89, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=A_62 | ~r1_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.01/4.07  tff(c_100, plain, (k4_xboole_0('#skF_3', '#skF_2')='#skF_3'), inference(resolution, [status(thm)], [c_72, c_89])).
% 10.01/4.07  tff(c_382, plain, (![A_83, B_84]: (k3_subset_1(A_83, k3_subset_1(A_83, B_84))=B_84 | ~m1_subset_1(B_84, k1_zfmisc_1(A_83)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 10.01/4.07  tff(c_388, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_50, c_382])).
% 10.01/4.07  tff(c_556, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/4.07  tff(c_564, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_556])).
% 10.01/4.07  tff(c_14, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.07  tff(c_591, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_564, c_14])).
% 10.01/4.07  tff(c_794, plain, (![A_104, B_105]: (m1_subset_1(k3_subset_1(A_104, B_105), k1_zfmisc_1(A_104)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 10.01/4.07  tff(c_34, plain, (![A_45, B_46]: (k4_xboole_0(A_45, B_46)=k3_subset_1(A_45, B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.01/4.07  tff(c_18176, plain, (![A_289, B_290]: (k4_xboole_0(A_289, k3_subset_1(A_289, B_290))=k3_subset_1(A_289, k3_subset_1(A_289, B_290)) | ~m1_subset_1(B_290, k1_zfmisc_1(A_289)))), inference(resolution, [status(thm)], [c_794, c_34])).
% 10.01/4.07  tff(c_18184, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_18176])).
% 10.01/4.07  tff(c_18191, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_388, c_591, c_18184])).
% 10.01/4.07  tff(c_563, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_52, c_556])).
% 10.01/4.07  tff(c_429, plain, (![A_87, B_88, C_89]: (k4_xboole_0(k4_xboole_0(A_87, B_88), C_89)=k4_xboole_0(A_87, k2_xboole_0(B_88, C_89)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/4.07  tff(c_477, plain, (![A_12, B_13, C_89]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_89))=k4_xboole_0(k3_xboole_0(A_12, B_13), C_89))), inference(superposition, [status(thm), theory('equality')], [c_14, c_429])).
% 10.01/4.07  tff(c_1300, plain, (![A_118, B_119, C_120]: (k3_xboole_0(k4_xboole_0(A_118, B_119), k4_xboole_0(A_118, C_120))=k4_xboole_0(A_118, k2_xboole_0(B_119, C_120)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.01/4.07  tff(c_1413, plain, (![A_12, B_13, C_120]: (k4_xboole_0(A_12, k2_xboole_0(k4_xboole_0(A_12, B_13), C_120))=k3_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1300])).
% 10.01/4.07  tff(c_13341, plain, (![A_258, B_259, C_260]: (k3_xboole_0(k3_xboole_0(A_258, B_259), k4_xboole_0(A_258, C_260))=k4_xboole_0(k3_xboole_0(A_258, B_259), C_260))), inference(demodulation, [status(thm), theory('equality')], [c_477, c_1413])).
% 10.01/4.07  tff(c_13674, plain, (![B_259]: (k3_xboole_0(k3_xboole_0('#skF_1', B_259), k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0(k3_xboole_0('#skF_1', B_259), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_563, c_13341])).
% 10.01/4.07  tff(c_18205, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_18191, c_13674])).
% 10.01/4.07  tff(c_18249, plain, (k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_100, c_18191, c_18205])).
% 10.01/4.07  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.01/4.07  tff(c_143, plain, (![A_70, B_71]: (k4_xboole_0(k2_xboole_0(A_70, B_71), B_71)=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/4.07  tff(c_150, plain, (![A_70]: (k4_xboole_0(A_70, k1_xboole_0)=k2_xboole_0(A_70, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_143, c_6])).
% 10.01/4.07  tff(c_159, plain, (![A_70]: (k2_xboole_0(A_70, k1_xboole_0)=A_70)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_150])).
% 10.01/4.07  tff(c_10, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k4_xboole_0(A_7, B_8), C_9)=k4_xboole_0(A_7, k2_xboole_0(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.01/4.07  tff(c_568, plain, (![C_9]: (k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_9)=k4_xboole_0('#skF_1', k2_xboole_0('#skF_2', C_9)))), inference(superposition, [status(thm), theory('equality')], [c_563, c_10])).
% 10.01/4.07  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.01/4.07  tff(c_180, plain, (![A_73, B_74]: (k4_xboole_0(A_73, k4_xboole_0(A_73, B_74))=k3_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.01/4.07  tff(c_207, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k3_xboole_0(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_180])).
% 10.01/4.07  tff(c_210, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_207])).
% 10.01/4.07  tff(c_496, plain, (![A_4, C_89]: (k4_xboole_0(A_4, k2_xboole_0(k1_xboole_0, C_89))=k4_xboole_0(A_4, C_89))), inference(superposition, [status(thm), theory('equality')], [c_6, c_429])).
% 10.01/4.07  tff(c_1443, plain, (![A_4, C_120]: (k4_xboole_0(A_4, k2_xboole_0(k1_xboole_0, C_120))=k3_xboole_0(A_4, k4_xboole_0(A_4, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1300])).
% 10.01/4.07  tff(c_1472, plain, (![A_4, C_120]: (k3_xboole_0(A_4, k4_xboole_0(A_4, C_120))=k4_xboole_0(A_4, C_120))), inference(demodulation, [status(thm), theory('equality')], [c_496, c_1443])).
% 10.01/4.07  tff(c_189, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k3_xboole_0(A_12, k4_xboole_0(A_12, B_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_180])).
% 10.01/4.07  tff(c_3444, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(demodulation, [status(thm), theory('equality')], [c_1472, c_189])).
% 10.01/4.07  tff(c_19219, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18249, c_3444])).
% 10.01/4.07  tff(c_19252, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_210, c_19219])).
% 10.01/4.07  tff(c_256, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k4_xboole_0(B_78, A_77))=B_78 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.01/4.07  tff(c_8, plain, (![A_5, B_6]: (k4_xboole_0(k2_xboole_0(A_5, B_6), B_6)=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.01/4.07  tff(c_262, plain, (![B_78, A_77]: (k4_xboole_0(B_78, k4_xboole_0(B_78, A_77))=k4_xboole_0(A_77, k4_xboole_0(B_78, A_77)) | ~r1_tarski(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_256, c_8])).
% 10.01/4.07  tff(c_288, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(B_78, A_77))=k3_xboole_0(B_78, A_77) | ~r1_tarski(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_262])).
% 10.01/4.07  tff(c_20197, plain, (k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_19252, c_288])).
% 10.01/4.07  tff(c_20265, plain, (k3_subset_1('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5036, c_18249, c_563, c_159, c_568, c_20197])).
% 10.01/4.07  tff(c_387, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_52, c_382])).
% 10.01/4.07  tff(c_20314, plain, (k3_subset_1('#skF_1', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20265, c_387])).
% 10.01/4.07  tff(c_20336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_20314])).
% 10.01/4.07  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.01/4.07  
% 10.01/4.07  Inference rules
% 10.01/4.07  ----------------------
% 10.01/4.07  #Ref     : 0
% 10.01/4.07  #Sup     : 5244
% 10.01/4.07  #Fact    : 0
% 10.01/4.07  #Define  : 0
% 10.01/4.07  #Split   : 12
% 10.01/4.07  #Chain   : 0
% 10.01/4.07  #Close   : 0
% 10.01/4.07  
% 10.01/4.07  Ordering : KBO
% 10.01/4.07  
% 10.01/4.07  Simplification rules
% 10.01/4.07  ----------------------
% 10.01/4.07  #Subsume      : 865
% 10.01/4.07  #Demod        : 4578
% 10.01/4.07  #Tautology    : 2321
% 10.01/4.07  #SimpNegUnit  : 213
% 10.01/4.07  #BackRed      : 40
% 10.01/4.07  
% 10.01/4.07  #Partial instantiations: 0
% 10.01/4.07  #Strategies tried      : 1
% 10.01/4.07  
% 10.01/4.07  Timing (in seconds)
% 10.01/4.07  ----------------------
% 10.01/4.07  Preprocessing        : 0.32
% 10.01/4.07  Parsing              : 0.17
% 10.01/4.07  CNF conversion       : 0.02
% 10.01/4.07  Main loop            : 2.97
% 10.01/4.07  Inferencing          : 0.63
% 10.01/4.07  Reduction            : 1.61
% 10.01/4.07  Demodulation         : 1.34
% 10.01/4.07  BG Simplification    : 0.08
% 10.01/4.07  Subsumption          : 0.49
% 10.01/4.07  Abstraction          : 0.13
% 10.01/4.07  MUC search           : 0.00
% 10.01/4.07  Cooper               : 0.00
% 10.01/4.07  Total                : 3.32
% 10.01/4.07  Index Insertion      : 0.00
% 10.01/4.07  Index Deletion       : 0.00
% 10.01/4.07  Index Matching       : 0.00
% 10.01/4.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
