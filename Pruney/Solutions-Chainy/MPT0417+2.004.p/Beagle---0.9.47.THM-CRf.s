%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:50 EST 2020

% Result     : Theorem 7.66s
% Output     : CNFRefutation 7.66s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 335 expanded)
%              Number of leaves         :   27 ( 122 expanded)
%              Depth                    :   17
%              Number of atoms          :  104 ( 508 expanded)
%              Number of equality atoms :   54 ( 236 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ( B != k1_xboole_0
         => k5_setfam_1(A,k7_setfam_1(A,B)) = k7_subset_1(A,k2_subset_1(A),k6_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_setfam_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ~ ( B != k1_xboole_0
          & k7_setfam_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_setfam_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k7_setfam_1(A,k7_setfam_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k7_setfam_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k7_setfam_1(A,B),k1_zfmisc_1(k1_zfmisc_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( B != k1_xboole_0
       => k7_subset_1(A,k2_subset_1(A),k5_setfam_1(A,B)) = k6_setfam_1(A,k7_setfam_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_setfam_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k5_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_setfam_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_304,plain,(
    ! [A_51,B_52] :
      ( k7_setfam_1(A_51,B_52) != k1_xboole_0
      | k1_xboole_0 = B_52
      | ~ m1_subset_1(B_52,k1_zfmisc_1(k1_zfmisc_1(A_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_332,plain,
    ( k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_304])).

tff(c_346,plain,(
    k7_setfam_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_332])).

tff(c_504,plain,(
    ! [A_60,B_61] :
      ( k7_setfam_1(A_60,k7_setfam_1(A_60,B_61)) = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_542,plain,(
    k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_504])).

tff(c_596,plain,(
    ! [A_64,B_65] :
      ( m1_subset_1(k7_setfam_1(A_64,B_65),k1_zfmisc_1(k1_zfmisc_1(A_64)))
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k3_subset_1(A_8,k3_subset_1(A_8,B_9)) = B_9
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_628,plain,(
    ! [A_64,B_65] :
      ( k3_subset_1(k1_zfmisc_1(A_64),k3_subset_1(k1_zfmisc_1(A_64),k7_setfam_1(A_64,B_65))) = k7_setfam_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(k1_zfmisc_1(A_64))) ) ),
    inference(resolution,[status(thm)],[c_596,c_10])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( k4_xboole_0(A_2,B_3) = k3_subset_1(A_2,B_3)
      | ~ m1_subset_1(B_3,k1_zfmisc_1(A_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3568,plain,(
    ! [A_151,B_152] :
      ( k4_xboole_0(k1_zfmisc_1(A_151),k7_setfam_1(A_151,B_152)) = k3_subset_1(k1_zfmisc_1(A_151),k7_setfam_1(A_151,B_152))
      | ~ m1_subset_1(B_152,k1_zfmisc_1(k1_zfmisc_1(A_151))) ) ),
    inference(resolution,[status(thm)],[c_596,c_4])).

tff(c_3687,plain,(
    k4_xboole_0(k1_zfmisc_1('#skF_1'),k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1(k1_zfmisc_1('#skF_1'),k7_setfam_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_3568])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k2_subset_1(A_4),k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_4] : m1_subset_1(A_4,k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_84,plain,(
    ! [A_31,B_32,C_33] :
      ( k7_subset_1(A_31,B_32,C_33) = k4_xboole_0(B_32,C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_90,plain,(
    ! [A_4,C_33] : k7_subset_1(A_4,A_4,C_33) = k4_xboole_0(A_4,C_33) ),
    inference(resolution,[status(thm)],[c_29,c_84])).

tff(c_109,plain,(
    ! [A_37,B_38,C_39] :
      ( m1_subset_1(k7_subset_1(A_37,B_38,C_39),k1_zfmisc_1(A_37))
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_4,C_33] :
      ( m1_subset_1(k4_xboole_0(A_4,C_33),k1_zfmisc_1(A_4))
      | ~ m1_subset_1(A_4,k1_zfmisc_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_109])).

tff(c_130,plain,(
    ! [A_40,C_41] : m1_subset_1(k4_xboole_0(A_40,C_41),k1_zfmisc_1(A_40)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_122])).

tff(c_260,plain,(
    ! [A_49,C_50] : k4_xboole_0(A_49,k4_xboole_0(A_49,C_50)) = k3_subset_1(A_49,k4_xboole_0(A_49,C_50)) ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_129,plain,(
    ! [A_4,C_33] : m1_subset_1(k4_xboole_0(A_4,C_33),k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_122])).

tff(c_276,plain,(
    ! [A_49,C_50] : m1_subset_1(k3_subset_1(A_49,k4_xboole_0(A_49,C_50)),k1_zfmisc_1(A_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_129])).

tff(c_3961,plain,(
    m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_1'),k3_subset_1(k1_zfmisc_1('#skF_1'),k7_setfam_1('#skF_1','#skF_2'))),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_3687,c_276])).

tff(c_5404,plain,
    ( m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_3961])).

tff(c_5420,plain,(
    m1_subset_1(k7_setfam_1('#skF_1','#skF_2'),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_5404])).

tff(c_22,plain,(
    ! [A_21,B_22] :
      ( k7_subset_1(A_21,k2_subset_1(A_21),k5_setfam_1(A_21,B_22)) = k6_setfam_1(A_21,k7_setfam_1(A_21,B_22))
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_21,B_22] :
      ( k7_subset_1(A_21,A_21,k5_setfam_1(A_21,B_22)) = k6_setfam_1(A_21,k7_setfam_1(A_21,B_22))
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_957,plain,(
    ! [A_21,B_22] :
      ( k6_setfam_1(A_21,k7_setfam_1(A_21,B_22)) = k4_xboole_0(A_21,k5_setfam_1(A_21,B_22))
      | k1_xboole_0 = B_22
      | ~ m1_subset_1(B_22,k1_zfmisc_1(k1_zfmisc_1(A_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_30])).

tff(c_5438,plain,
    ( k6_setfam_1('#skF_1',k7_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5420,c_957])).

tff(c_5465,plain,
    ( k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2')
    | k7_setfam_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_5438])).

tff(c_5466,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_346,c_5465])).

tff(c_145,plain,(
    ! [A_40,C_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,C_41)) = k3_subset_1(A_40,k4_xboole_0(A_40,C_41)) ),
    inference(resolution,[status(thm)],[c_130,c_4])).

tff(c_5513,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')))) = k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5466,c_145])).

tff(c_5530,plain,(
    k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5466,c_5513])).

tff(c_24,plain,(
    k7_subset_1('#skF_1',k2_subset_1('#skF_1'),k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_31,plain,(
    k7_subset_1('#skF_1','#skF_1',k6_setfam_1('#skF_1','#skF_2')) != k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_204,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k4_xboole_0('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_31])).

tff(c_5740,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) != k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5530,c_204])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k7_setfam_1(A_15,B_16),k1_zfmisc_1(k1_zfmisc_1(A_15)))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_147,plain,(
    ! [A_42,B_43] :
      ( m1_subset_1(k5_setfam_1(A_42,B_43),k1_zfmisc_1(A_42))
      | ~ m1_subset_1(B_43,k1_zfmisc_1(k1_zfmisc_1(A_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1216,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,k5_setfam_1(A_92,B_93)) = k3_subset_1(A_92,k5_setfam_1(A_92,B_93))
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(resolution,[status(thm)],[c_147,c_4])).

tff(c_7891,plain,(
    ! [A_228,B_229] :
      ( k4_xboole_0(A_228,k5_setfam_1(A_228,k7_setfam_1(A_228,B_229))) = k3_subset_1(A_228,k5_setfam_1(A_228,k7_setfam_1(A_228,B_229)))
      | ~ m1_subset_1(B_229,k1_zfmisc_1(k1_zfmisc_1(A_228))) ) ),
    inference(resolution,[status(thm)],[c_16,c_1216])).

tff(c_8035,plain,(
    k4_xboole_0('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_28,c_7891])).

tff(c_8101,plain,(
    k3_subset_1('#skF_1',k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2'))) = k6_setfam_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5466,c_8035])).

tff(c_1573,plain,(
    ! [A_99,B_100] :
      ( k3_subset_1(A_99,k3_subset_1(A_99,k5_setfam_1(A_99,B_100))) = k5_setfam_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(k1_zfmisc_1(A_99))) ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_1645,plain,(
    ! [A_15,B_16] :
      ( k3_subset_1(A_15,k3_subset_1(A_15,k5_setfam_1(A_15,k7_setfam_1(A_15,B_16)))) = k5_setfam_1(A_15,k7_setfam_1(A_15,B_16))
      | ~ m1_subset_1(B_16,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(resolution,[status(thm)],[c_16,c_1573])).

tff(c_8106,plain,
    ( k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_8101,c_1645])).

tff(c_8110,plain,(
    k5_setfam_1('#skF_1',k7_setfam_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k6_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8106])).

tff(c_8112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5740,c_8110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:02:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.66/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.81  
% 7.66/2.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.81  %$ m1_subset_1 > k7_subset_1 > k7_setfam_1 > k6_setfam_1 > k5_setfam_1 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 7.66/2.81  
% 7.66/2.81  %Foreground sorts:
% 7.66/2.81  
% 7.66/2.81  
% 7.66/2.81  %Background operators:
% 7.66/2.81  
% 7.66/2.81  
% 7.66/2.81  %Foreground operators:
% 7.66/2.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.66/2.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.66/2.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.66/2.81  tff(k7_setfam_1, type, k7_setfam_1: ($i * $i) > $i).
% 7.66/2.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 7.66/2.81  tff('#skF_2', type, '#skF_2': $i).
% 7.66/2.81  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 7.66/2.81  tff('#skF_1', type, '#skF_1': $i).
% 7.66/2.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.66/2.81  tff(k5_setfam_1, type, k5_setfam_1: ($i * $i) > $i).
% 7.66/2.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.66/2.81  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 7.66/2.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.66/2.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 7.66/2.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.66/2.81  
% 7.66/2.82  tff(f_80, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k5_setfam_1(A, k7_setfam_1(A, B)) = k7_subset_1(A, k2_subset_1(A), k6_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_setfam_1)).
% 7.66/2.82  tff(f_65, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ~(~(B = k1_xboole_0) & (k7_setfam_1(A, B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_setfam_1)).
% 7.66/2.82  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k7_setfam_1(A, k7_setfam_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k7_setfam_1)).
% 7.66/2.82  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k7_setfam_1(A, B), k1_zfmisc_1(k1_zfmisc_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_setfam_1)).
% 7.66/2.82  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 7.66/2.82  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 7.66/2.82  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 7.66/2.82  tff(f_33, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 7.66/2.82  tff(f_45, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 7.66/2.82  tff(f_37, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 7.66/2.82  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (~(B = k1_xboole_0) => (k7_subset_1(A, k2_subset_1(A), k5_setfam_1(A, B)) = k6_setfam_1(A, k7_setfam_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_setfam_1)).
% 7.66/2.82  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k5_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_setfam_1)).
% 7.66/2.82  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.82  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.82  tff(c_304, plain, (![A_51, B_52]: (k7_setfam_1(A_51, B_52)!=k1_xboole_0 | k1_xboole_0=B_52 | ~m1_subset_1(B_52, k1_zfmisc_1(k1_zfmisc_1(A_51))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.66/2.82  tff(c_332, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_28, c_304])).
% 7.66/2.82  tff(c_346, plain, (k7_setfam_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_26, c_332])).
% 7.66/2.82  tff(c_504, plain, (![A_60, B_61]: (k7_setfam_1(A_60, k7_setfam_1(A_60, B_61))=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.66/2.82  tff(c_542, plain, (k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_504])).
% 7.66/2.82  tff(c_596, plain, (![A_64, B_65]: (m1_subset_1(k7_setfam_1(A_64, B_65), k1_zfmisc_1(k1_zfmisc_1(A_64))) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.66/2.82  tff(c_10, plain, (![A_8, B_9]: (k3_subset_1(A_8, k3_subset_1(A_8, B_9))=B_9 | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.66/2.82  tff(c_628, plain, (![A_64, B_65]: (k3_subset_1(k1_zfmisc_1(A_64), k3_subset_1(k1_zfmisc_1(A_64), k7_setfam_1(A_64, B_65)))=k7_setfam_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(k1_zfmisc_1(A_64))))), inference(resolution, [status(thm)], [c_596, c_10])).
% 7.66/2.82  tff(c_4, plain, (![A_2, B_3]: (k4_xboole_0(A_2, B_3)=k3_subset_1(A_2, B_3) | ~m1_subset_1(B_3, k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.66/2.82  tff(c_3568, plain, (![A_151, B_152]: (k4_xboole_0(k1_zfmisc_1(A_151), k7_setfam_1(A_151, B_152))=k3_subset_1(k1_zfmisc_1(A_151), k7_setfam_1(A_151, B_152)) | ~m1_subset_1(B_152, k1_zfmisc_1(k1_zfmisc_1(A_151))))), inference(resolution, [status(thm)], [c_596, c_4])).
% 7.66/2.82  tff(c_3687, plain, (k4_xboole_0(k1_zfmisc_1('#skF_1'), k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1(k1_zfmisc_1('#skF_1'), k7_setfam_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_3568])).
% 7.66/2.82  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.66/2.82  tff(c_6, plain, (![A_4]: (m1_subset_1(k2_subset_1(A_4), k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.66/2.82  tff(c_29, plain, (![A_4]: (m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 7.66/2.82  tff(c_84, plain, (![A_31, B_32, C_33]: (k7_subset_1(A_31, B_32, C_33)=k4_xboole_0(B_32, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.66/2.82  tff(c_90, plain, (![A_4, C_33]: (k7_subset_1(A_4, A_4, C_33)=k4_xboole_0(A_4, C_33))), inference(resolution, [status(thm)], [c_29, c_84])).
% 7.66/2.82  tff(c_109, plain, (![A_37, B_38, C_39]: (m1_subset_1(k7_subset_1(A_37, B_38, C_39), k1_zfmisc_1(A_37)) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.66/2.82  tff(c_122, plain, (![A_4, C_33]: (m1_subset_1(k4_xboole_0(A_4, C_33), k1_zfmisc_1(A_4)) | ~m1_subset_1(A_4, k1_zfmisc_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_109])).
% 7.66/2.82  tff(c_130, plain, (![A_40, C_41]: (m1_subset_1(k4_xboole_0(A_40, C_41), k1_zfmisc_1(A_40)))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_122])).
% 7.66/2.82  tff(c_260, plain, (![A_49, C_50]: (k4_xboole_0(A_49, k4_xboole_0(A_49, C_50))=k3_subset_1(A_49, k4_xboole_0(A_49, C_50)))), inference(resolution, [status(thm)], [c_130, c_4])).
% 7.66/2.82  tff(c_129, plain, (![A_4, C_33]: (m1_subset_1(k4_xboole_0(A_4, C_33), k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_122])).
% 7.66/2.82  tff(c_276, plain, (![A_49, C_50]: (m1_subset_1(k3_subset_1(A_49, k4_xboole_0(A_49, C_50)), k1_zfmisc_1(A_49)))), inference(superposition, [status(thm), theory('equality')], [c_260, c_129])).
% 7.66/2.82  tff(c_3961, plain, (m1_subset_1(k3_subset_1(k1_zfmisc_1('#skF_1'), k3_subset_1(k1_zfmisc_1('#skF_1'), k7_setfam_1('#skF_1', '#skF_2'))), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_3687, c_276])).
% 7.66/2.82  tff(c_5404, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_628, c_3961])).
% 7.66/2.82  tff(c_5420, plain, (m1_subset_1(k7_setfam_1('#skF_1', '#skF_2'), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_5404])).
% 7.66/2.82  tff(c_22, plain, (![A_21, B_22]: (k7_subset_1(A_21, k2_subset_1(A_21), k5_setfam_1(A_21, B_22))=k6_setfam_1(A_21, k7_setfam_1(A_21, B_22)) | k1_xboole_0=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.66/2.82  tff(c_30, plain, (![A_21, B_22]: (k7_subset_1(A_21, A_21, k5_setfam_1(A_21, B_22))=k6_setfam_1(A_21, k7_setfam_1(A_21, B_22)) | k1_xboole_0=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 7.66/2.82  tff(c_957, plain, (![A_21, B_22]: (k6_setfam_1(A_21, k7_setfam_1(A_21, B_22))=k4_xboole_0(A_21, k5_setfam_1(A_21, B_22)) | k1_xboole_0=B_22 | ~m1_subset_1(B_22, k1_zfmisc_1(k1_zfmisc_1(A_21))))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_30])).
% 7.66/2.82  tff(c_5438, plain, (k6_setfam_1('#skF_1', k7_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))) | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_5420, c_957])).
% 7.66/2.82  tff(c_5465, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2') | k7_setfam_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_542, c_5438])).
% 7.66/2.82  tff(c_5466, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_346, c_5465])).
% 7.66/2.82  tff(c_145, plain, (![A_40, C_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, C_41))=k3_subset_1(A_40, k4_xboole_0(A_40, C_41)))), inference(resolution, [status(thm)], [c_130, c_4])).
% 7.66/2.82  tff(c_5513, plain, (k3_subset_1('#skF_1', k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))))=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_5466, c_145])).
% 7.66/2.82  tff(c_5530, plain, (k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5466, c_5513])).
% 7.66/2.82  tff(c_24, plain, (k7_subset_1('#skF_1', k2_subset_1('#skF_1'), k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 7.66/2.82  tff(c_31, plain, (k7_subset_1('#skF_1', '#skF_1', k6_setfam_1('#skF_1', '#skF_2'))!=k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 7.66/2.82  tff(c_204, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_31])).
% 7.66/2.82  tff(c_5740, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))!=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_5530, c_204])).
% 7.66/2.82  tff(c_16, plain, (![A_15, B_16]: (m1_subset_1(k7_setfam_1(A_15, B_16), k1_zfmisc_1(k1_zfmisc_1(A_15))) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.66/2.82  tff(c_147, plain, (![A_42, B_43]: (m1_subset_1(k5_setfam_1(A_42, B_43), k1_zfmisc_1(A_42)) | ~m1_subset_1(B_43, k1_zfmisc_1(k1_zfmisc_1(A_42))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.66/2.82  tff(c_1216, plain, (![A_92, B_93]: (k4_xboole_0(A_92, k5_setfam_1(A_92, B_93))=k3_subset_1(A_92, k5_setfam_1(A_92, B_93)) | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(resolution, [status(thm)], [c_147, c_4])).
% 7.66/2.82  tff(c_7891, plain, (![A_228, B_229]: (k4_xboole_0(A_228, k5_setfam_1(A_228, k7_setfam_1(A_228, B_229)))=k3_subset_1(A_228, k5_setfam_1(A_228, k7_setfam_1(A_228, B_229))) | ~m1_subset_1(B_229, k1_zfmisc_1(k1_zfmisc_1(A_228))))), inference(resolution, [status(thm)], [c_16, c_1216])).
% 7.66/2.82  tff(c_8035, plain, (k4_xboole_0('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_28, c_7891])).
% 7.66/2.82  tff(c_8101, plain, (k3_subset_1('#skF_1', k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2')))=k6_setfam_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5466, c_8035])).
% 7.66/2.82  tff(c_1573, plain, (![A_99, B_100]: (k3_subset_1(A_99, k3_subset_1(A_99, k5_setfam_1(A_99, B_100)))=k5_setfam_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(k1_zfmisc_1(A_99))))), inference(resolution, [status(thm)], [c_147, c_10])).
% 7.66/2.82  tff(c_1645, plain, (![A_15, B_16]: (k3_subset_1(A_15, k3_subset_1(A_15, k5_setfam_1(A_15, k7_setfam_1(A_15, B_16))))=k5_setfam_1(A_15, k7_setfam_1(A_15, B_16)) | ~m1_subset_1(B_16, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(resolution, [status(thm)], [c_16, c_1573])).
% 7.66/2.82  tff(c_8106, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2')) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_8101, c_1645])).
% 7.66/2.82  tff(c_8110, plain, (k5_setfam_1('#skF_1', k7_setfam_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k6_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8106])).
% 7.66/2.82  tff(c_8112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5740, c_8110])).
% 7.66/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.66/2.82  
% 7.66/2.82  Inference rules
% 7.66/2.82  ----------------------
% 7.66/2.82  #Ref     : 0
% 7.66/2.82  #Sup     : 2105
% 7.66/2.82  #Fact    : 0
% 7.66/2.82  #Define  : 0
% 7.66/2.82  #Split   : 7
% 7.66/2.82  #Chain   : 0
% 7.66/2.82  #Close   : 0
% 7.66/2.82  
% 7.66/2.82  Ordering : KBO
% 7.66/2.82  
% 7.66/2.82  Simplification rules
% 7.66/2.82  ----------------------
% 7.66/2.82  #Subsume      : 101
% 7.66/2.82  #Demod        : 912
% 7.66/2.82  #Tautology    : 497
% 7.66/2.82  #SimpNegUnit  : 27
% 7.66/2.82  #BackRed      : 6
% 7.66/2.82  
% 7.66/2.82  #Partial instantiations: 0
% 7.66/2.82  #Strategies tried      : 1
% 7.66/2.82  
% 7.66/2.82  Timing (in seconds)
% 7.66/2.82  ----------------------
% 7.66/2.83  Preprocessing        : 0.31
% 7.66/2.83  Parsing              : 0.17
% 7.66/2.83  CNF conversion       : 0.02
% 7.66/2.83  Main loop            : 1.75
% 7.66/2.83  Inferencing          : 0.46
% 7.66/2.83  Reduction            : 0.72
% 7.66/2.83  Demodulation         : 0.56
% 7.66/2.83  BG Simplification    : 0.07
% 7.66/2.83  Subsumption          : 0.34
% 7.66/2.83  Abstraction          : 0.12
% 7.66/2.83  MUC search           : 0.00
% 7.66/2.83  Cooper               : 0.00
% 7.66/2.83  Total                : 2.10
% 7.66/2.83  Index Insertion      : 0.00
% 7.66/2.83  Index Deletion       : 0.00
% 7.66/2.83  Index Matching       : 0.00
% 7.66/2.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
