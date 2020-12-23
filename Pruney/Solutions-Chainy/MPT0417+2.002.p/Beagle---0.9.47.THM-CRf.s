%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 9.64s
% Output     : CNFRefutation 9.71s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 488 expanded)
%              Number of leaves         :   29 ( 177 expanded)
%              Depth                    :   18
%              Number of atoms          :  109 ( 879 expanded)
%              Number of equality atoms :   54 ( 447 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k7_setfam_1,type,(
    k7_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k5_setfam_1,type,(
    k5_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_29,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( m1_subset_1(k7_setfam_1(A_16,B_17),k1_zfmisc_1(k1_zfmisc_1(A_16)))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_127,plain,(
    ! [A_38,B_39] :
      ( k7_setfam_1(A_38,B_39) != k1_xboole_0
      | k1_xboole_0 = B_39
      | ~ m1_subset_1(B_39,k1_zfmisc_1(k1_zfmisc_1(A_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_134,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_127])).

tff(c_142,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_134])).

tff(c_154,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k5_setfam_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_334,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,k5_setfam_1(A_59,B_60)) = k3_subset_1(A_59,k5_setfam_1(A_59,B_60))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(k1_zfmisc_1(A_59))) ) ),
    inference(resolution,[status(thm)],[c_154,c_6])).

tff(c_2972,plain,(
    ! [A_181,B_182] :
      ( k4_xboole_0(A_181,k5_setfam_1(A_181,k7_setfam_1(A_181,B_182))) = k3_subset_1(A_181,k5_setfam_1(A_181,k7_setfam_1(A_181,B_182)))
      | ~ m1_subset_1(B_182,k1_zfmisc_1(k1_zfmisc_1(A_181))) ) ),
    inference(resolution,[status(thm)],[c_18,c_334])).

tff(c_3004,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_30,c_2972])).

tff(c_111,plain,(
    ! [A_36,B_37] :
      ( k7_setfam_1(A_36,k7_setfam_1(A_36,B_37)) = B_37
      | ~ m1_subset_1(B_37,k1_zfmisc_1(k1_zfmisc_1(A_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_121,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_111])).

tff(c_4,plain,(
    ! [A_3] : k2_subset_1(A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k2_subset_1(A_6),k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    ! [A_6] : m1_subset_1(A_6,k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_171,plain,(
    ! [A_44,B_45,C_46] :
      ( k7_subset_1(A_44,B_45,C_46) = k4_xboole_0(B_45,C_46)
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_183,plain,(
    ! [A_6,C_46] : k7_subset_1(A_6,A_6,C_46) = k4_xboole_0(A_6,C_46) ),
    inference(resolution,[status(thm)],[c_31,c_171])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k7_subset_1(A_22,k2_subset_1(A_22),k5_setfam_1(A_22,B_23)) = k6_setfam_1(A_22,k7_setfam_1(A_22,B_23))
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_22,B_23] :
      ( k7_subset_1(A_22,A_22,k5_setfam_1(A_22,B_23)) = k6_setfam_1(A_22,k7_setfam_1(A_22,B_23))
      | k1_xboole_0 = B_23
      | ~ m1_subset_1(B_23,k1_zfmisc_1(k1_zfmisc_1(A_22))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_24])).

tff(c_230,plain,(
    ! [A_52,B_53] :
      ( k6_setfam_1(A_52,k7_setfam_1(A_52,B_53)) = k4_xboole_0(A_52,k5_setfam_1(A_52,B_53))
      | k1_xboole_0 = B_53
      | ~ m1_subset_1(B_53,k1_zfmisc_1(k1_zfmisc_1(A_52))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_32])).

tff(c_10641,plain,(
    ! [A_354,B_355] :
      ( k6_setfam_1(A_354,k7_setfam_1(A_354,k7_setfam_1(A_354,B_355))) = k4_xboole_0(A_354,k5_setfam_1(A_354,k7_setfam_1(A_354,B_355)))
      | k7_setfam_1(A_354,B_355) = k1_xboole_0
      | ~ m1_subset_1(B_355,k1_zfmisc_1(k1_zfmisc_1(A_354))) ) ),
    inference(resolution,[status(thm)],[c_18,c_230])).

tff(c_10675,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_10641])).

tff(c_10698,plain,
    ( k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3004,c_121,c_10675])).

tff(c_10699,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_10698])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( k3_subset_1(A_9,k3_subset_1(A_9,B_10)) = B_10
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_547,plain,(
    ! [A_77,B_78] :
      ( k3_subset_1(A_77,k3_subset_1(A_77,k5_setfam_1(A_77,B_78))) = k5_setfam_1(A_77,B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(k1_zfmisc_1(A_77))) ) ),
    inference(resolution,[status(thm)],[c_154,c_12])).

tff(c_564,plain,(
    ! [A_16,B_17] :
      ( k3_subset_1(A_16,k3_subset_1(A_16,k5_setfam_1(A_16,k7_setfam_1(A_16,B_17)))) = k5_setfam_1(A_16,k7_setfam_1(A_16,B_17))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(k1_zfmisc_1(A_16))) ) ),
    inference(resolution,[status(thm)],[c_18,c_547])).

tff(c_10709,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10699,c_564])).

tff(c_10723,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_10709])).

tff(c_26,plain,(
    k7_subset_1('#skF_1',k2_subset_1('#skF_1'),k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_33,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_184,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_33])).

tff(c_10734,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10723,c_184])).

tff(c_10732,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10723,c_10699])).

tff(c_10,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k3_subset_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_85,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_303,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,k3_subset_1(A_56,B_57)) = k3_subset_1(A_56,k3_subset_1(A_56,B_57))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_316,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,k3_subset_1(A_7,k3_subset_1(A_7,B_8))) = k3_subset_1(A_7,k3_subset_1(A_7,k3_subset_1(A_7,B_8)))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(A_7)) ) ),
    inference(resolution,[status(thm)],[c_10,c_303])).

tff(c_10772,plain,
    ( k3_subset_1('#skF_1',k3_subset_1('#skF_1',k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')))) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10732,c_316])).

tff(c_10787,plain,
    ( k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10732,c_10772])).

tff(c_10788,plain,(
    ~ m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_10734,c_10787])).

tff(c_10718,plain,
    ( m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10699,c_10])).

tff(c_10792,plain,
    ( m1_subset_1(k6_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10723,c_10718])).

tff(c_10793,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_10788,c_10792])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k5_setfam_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10741,plain,
    ( m1_subset_1(k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_10723,c_16])).

tff(c_11004,plain,(
    ~ m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(negUnitSimplification,[status(thm)],[c_10793,c_10741])).

tff(c_11007,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_18,c_11004])).

tff(c_11011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_11007])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.64/3.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.60  
% 9.64/3.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.64/3.60  %$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_xboole_0 > k5_setfam_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 9.64/3.60  
% 9.64/3.60  %Foreground sorts:
% 9.64/3.60  
% 9.64/3.60  
% 9.64/3.60  %Background operators:
% 9.64/3.60  
% 9.64/3.60  
% 9.64/3.60  %Foreground operators:
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.64/3.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.64/3.60  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 9.64/3.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 9.64/3.60  tff('#skF_2', type, '#skF_2': $i).
% 9.64/3.60  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 9.64/3.60  tff('#skF_1', type, '#skF_1': $i).
% 9.64/3.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.64/3.60  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.64/3.60  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 9.64/3.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.64/3.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.64/3.60  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 9.64/3.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.64/3.60  
% 9.71/3.61  tff(f_82, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 9.71/3.61  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 9.71/3.61  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 9.71/3.61  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 9.71/3.61  tff(f_33, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 9.71/3.61  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 9.71/3.61  tff(f_29, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 9.71/3.61  tff(f_35, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 9.71/3.61  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 9.71/3.61  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 9.71/3.61  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 9.71/3.61  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 9.71/3.61  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.71/3.61  tff(c_18, plain, (![A_16, B_17]: (m1_subset_1(k7_setfam_1(A_16, B_17), k1_zfmisc_1(k1_zfmisc_1(A_16))) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 9.71/3.61  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.71/3.61  tff(c_127, plain, (![A_38, B_39]: (k7_setfam_1(A_38, B_39)!=k1_xboole_0 | k1_xboole_0=B_39 | ~m1_subset_1(B_39, k1_zfmisc_1(k1_zfmisc_1(A_38))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.71/3.61  tff(c_134, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_127])).
% 9.71/3.61  tff(c_142, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_28, c_134])).
% 9.71/3.61  tff(c_154, plain, (![A_42, B_43]: (m1_subset_1(k5_setfam_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.71/3.61  tff(c_6, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.61  tff(c_334, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k5_setfam_1(A_59, B_60))=k3_subset_1(A_59, k5_setfam_1(A_59, B_60)) | ~m1_subset_1(B_60, k1_zfmisc_1(k1_zfmisc_1(A_59))))), inference(resolution, [status(thm)], [c_154, c_6])).
% 9.71/3.61  tff(c_2972, plain, (![A_181, B_182]: (k4_xboole_0(A_181, k5_setfam_1(A_181, k7_setfam_1(A_181, B_182)))=k3_subset_1(A_181, k5_setfam_1(A_181, k7_setfam_1(A_181, B_182))) | ~m1_subset_1(B_182, k1_zfmisc_1(k1_zfmisc_1(A_181))))), inference(resolution, [status(thm)], [c_18, c_334])).
% 9.71/3.61  tff(c_3004, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_30, c_2972])).
% 9.71/3.61  tff(c_111, plain, (![A_36, B_37]: (k7_setfam_1(A_36, k7_setfam_1(A_36, B_37))=B_37 | ~m1_subset_1(B_37, k1_zfmisc_1(k1_zfmisc_1(A_36))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.71/3.61  tff(c_121, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_30, c_111])).
% 9.71/3.61  tff(c_4, plain, (![A_3]: (k2_subset_1(A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.71/3.61  tff(c_8, plain, (![A_6]: (m1_subset_1(k2_subset_1(A_6), k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.71/3.61  tff(c_31, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 9.71/3.61  tff(c_171, plain, (![A_44, B_45, C_46]: (k7_subset_1(A_44, B_45, C_46)=k4_xboole_0(B_45, C_46) | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.71/3.61  tff(c_183, plain, (![A_6, C_46]: (k7_subset_1(A_6, A_6, C_46)=k4_xboole_0(A_6, C_46))), inference(resolution, [status(thm)], [c_31, c_171])).
% 9.71/3.61  tff(c_24, plain, (![A_22, B_23]: (k7_subset_1(A_22, k2_subset_1(A_22), k5_setfam_1(A_22, B_23))=k6_setfam_1(A_22, k7_setfam_1(A_22, B_23)) | k1_xboole_0=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.71/3.61  tff(c_32, plain, (![A_22, B_23]: (k7_subset_1(A_22, A_22, k5_setfam_1(A_22, B_23))=k6_setfam_1(A_22, k7_setfam_1(A_22, B_23)) | k1_xboole_0=B_23 | ~m1_subset_1(B_23, k1_zfmisc_1(k1_zfmisc_1(A_22))))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_24])).
% 9.71/3.61  tff(c_230, plain, (![A_52, B_53]: (k6_setfam_1(A_52, k7_setfam_1(A_52, B_53))=k4_xboole_0(A_52, k5_setfam_1(A_52, B_53)) | k1_xboole_0=B_53 | ~m1_subset_1(B_53, k1_zfmisc_1(k1_zfmisc_1(A_52))))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_32])).
% 9.71/3.61  tff(c_10641, plain, (![A_354, B_355]: (k6_setfam_1(A_354, k7_setfam_1(A_354, k7_setfam_1(A_354, B_355)))=k4_xboole_0(A_354, k5_setfam_1(A_354, k7_setfam_1(A_354, B_355))) | k7_setfam_1(A_354, B_355)=k1_xboole_0 | ~m1_subset_1(B_355, k1_zfmisc_1(k1_zfmisc_1(A_354))))), inference(resolution, [status(thm)], [c_18, c_230])).
% 9.71/3.61  tff(c_10675, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_10641])).
% 9.71/3.61  tff(c_10698, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3004, c_121, c_10675])).
% 9.71/3.61  tff(c_10699, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_142, c_10698])).
% 9.71/3.61  tff(c_12, plain, (![A_9, B_10]: (k3_subset_1(A_9, k3_subset_1(A_9, B_10))=B_10 | ~m1_subset_1(B_10, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.71/3.61  tff(c_547, plain, (![A_77, B_78]: (k3_subset_1(A_77, k3_subset_1(A_77, k5_setfam_1(A_77, B_78)))=k5_setfam_1(A_77, B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(k1_zfmisc_1(A_77))))), inference(resolution, [status(thm)], [c_154, c_12])).
% 9.71/3.61  tff(c_564, plain, (![A_16, B_17]: (k3_subset_1(A_16, k3_subset_1(A_16, k5_setfam_1(A_16, k7_setfam_1(A_16, B_17))))=k5_setfam_1(A_16, k7_setfam_1(A_16, B_17)) | ~m1_subset_1(B_17, k1_zfmisc_1(k1_zfmisc_1(A_16))))), inference(resolution, [status(thm)], [c_18, c_547])).
% 9.71/3.61  tff(c_10709, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10699, c_564])).
% 9.71/3.61  tff(c_10723, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_10709])).
% 9.71/3.61  tff(c_26, plain, (k7_subset_1('#skF_1', k2_subset_1('#skF_1'), k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 9.71/3.61  tff(c_33, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 9.71/3.61  tff(c_184, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_33])).
% 9.71/3.61  tff(c_10734, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10723, c_184])).
% 9.71/3.61  tff(c_10732, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10723, c_10699])).
% 9.71/3.61  tff(c_10, plain, (![A_7, B_8]: (m1_subset_1(k3_subset_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.71/3.61  tff(c_85, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.71/3.61  tff(c_303, plain, (![A_56, B_57]: (k4_xboole_0(A_56, k3_subset_1(A_56, B_57))=k3_subset_1(A_56, k3_subset_1(A_56, B_57)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_10, c_85])).
% 9.71/3.61  tff(c_316, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_subset_1(A_7, k3_subset_1(A_7, B_8)))=k3_subset_1(A_7, k3_subset_1(A_7, k3_subset_1(A_7, B_8))) | ~m1_subset_1(B_8, k1_zfmisc_1(A_7)))), inference(resolution, [status(thm)], [c_10, c_303])).
% 9.71/3.61  tff(c_10772, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10732, c_316])).
% 9.71/3.61  tff(c_10787, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10732, c_10772])).
% 9.71/3.61  tff(c_10788, plain, (~m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_10734, c_10787])).
% 9.71/3.61  tff(c_10718, plain, (m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_10699, c_10])).
% 9.71/3.61  tff(c_10792, plain, (m1_subset_1(k6_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10723, c_10718])).
% 9.71/3.61  tff(c_10793, plain, (~m1_subset_1(k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_10788, c_10792])).
% 9.71/3.61  tff(c_16, plain, (![A_14, B_15]: (m1_subset_1(k5_setfam_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.71/3.61  tff(c_10741, plain, (m1_subset_1(k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_10723, c_16])).
% 9.71/3.61  tff(c_11004, plain, (~m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(negUnitSimplification, [status(thm)], [c_10793, c_10741])).
% 9.71/3.61  tff(c_11007, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_11004])).
% 9.71/3.61  tff(c_11011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_11007])).
% 9.71/3.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.71/3.61  
% 9.71/3.61  Inference rules
% 9.71/3.61  ----------------------
% 9.71/3.61  #Ref     : 0
% 9.71/3.61  #Sup     : 2980
% 9.71/3.61  #Fact    : 0
% 9.71/3.61  #Define  : 0
% 9.71/3.61  #Split   : 3
% 9.71/3.61  #Chain   : 0
% 9.71/3.61  #Close   : 0
% 9.71/3.61  
% 9.71/3.61  Ordering : KBO
% 9.71/3.61  
% 9.71/3.61  Simplification rules
% 9.71/3.61  ----------------------
% 9.71/3.61  #Subsume      : 491
% 9.71/3.61  #Demod        : 692
% 9.71/3.61  #Tautology    : 689
% 9.71/3.61  #SimpNegUnit  : 10
% 9.71/3.61  #BackRed      : 7
% 9.71/3.61  
% 9.71/3.61  #Partial instantiations: 0
% 9.71/3.61  #Strategies tried      : 1
% 9.71/3.61  
% 9.71/3.61  Timing (in seconds)
% 9.71/3.61  ----------------------
% 9.71/3.62  Preprocessing        : 0.31
% 9.71/3.62  Parsing              : 0.17
% 9.71/3.62  CNF conversion       : 0.02
% 9.71/3.62  Main loop            : 2.52
% 9.71/3.62  Inferencing          : 0.82
% 9.71/3.62  Reduction            : 0.70
% 9.71/3.62  Demodulation         : 0.51
% 9.71/3.62  BG Simplification    : 0.10
% 9.71/3.62  Subsumption          : 0.74
% 9.71/3.62  Abstraction          : 0.14
% 9.71/3.62  MUC search           : 0.00
% 9.71/3.62  Cooper               : 0.00
% 9.71/3.62  Total                : 2.87
% 9.71/3.62  Index Insertion      : 0.00
% 9.71/3.62  Index Deletion       : 0.00
% 9.71/3.62  Index Matching       : 0.00
% 9.71/3.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
