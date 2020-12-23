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
% DateTime   : Thu Dec  3 10:07:58 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.82s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 189 expanded)
%              Number of leaves         :   28 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  158 ( 364 expanded)
%              Number of equality atoms :   67 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
       => ( k7_relset_1(B,A,C,k8_relset_1(B,A,C,A)) = k2_relset_1(B,A,C)
          & k8_relset_1(B,A,C,k7_relset_1(B,A,C,B)) = k1_relset_1(B,A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_29,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_33,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_408,plain,(
    ! [C_118,A_119,B_120] :
      ( m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_120)))
      | ~ r1_tarski(k2_relat_1(C_118),B_120)
      | ~ r1_tarski(k1_relat_1(C_118),A_119)
      | ~ v1_relat_1(C_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    ! [A_23,B_24,C_25] :
      ( k8_relset_1(A_23,B_24,C_25,B_24) = k1_relset_1(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_509,plain,(
    ! [A_151,B_152,C_153] :
      ( k8_relset_1(A_151,B_152,C_153,B_152) = k1_relset_1(A_151,B_152,C_153)
      | ~ r1_tarski(k2_relat_1(C_153),B_152)
      | ~ r1_tarski(k1_relat_1(C_153),A_151)
      | ~ v1_relat_1(C_153) ) ),
    inference(resolution,[status(thm)],[c_408,c_20])).

tff(c_514,plain,(
    ! [A_154,C_155] :
      ( k8_relset_1(A_154,k2_relat_1(C_155),C_155,k2_relat_1(C_155)) = k1_relset_1(A_154,k2_relat_1(C_155),C_155)
      | ~ r1_tarski(k1_relat_1(C_155),A_154)
      | ~ v1_relat_1(C_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_509])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( k8_relset_1(A_16,B_17,C_18,D_19) = k10_relat_1(C_18,D_19)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_481,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k8_relset_1(A_140,B_141,C_142,D_143) = k10_relat_1(C_142,D_143)
      | ~ r1_tarski(k2_relat_1(C_142),B_141)
      | ~ r1_tarski(k1_relat_1(C_142),A_140)
      | ~ v1_relat_1(C_142) ) ),
    inference(resolution,[status(thm)],[c_408,c_16])).

tff(c_495,plain,(
    ! [A_146,C_147,D_148] :
      ( k8_relset_1(A_146,k2_relat_1(C_147),C_147,D_148) = k10_relat_1(C_147,D_148)
      | ~ r1_tarski(k1_relat_1(C_147),A_146)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_6,c_481])).

tff(c_499,plain,(
    ! [C_147,D_148] :
      ( k8_relset_1(k1_relat_1(C_147),k2_relat_1(C_147),C_147,D_148) = k10_relat_1(C_147,D_148)
      | ~ v1_relat_1(C_147) ) ),
    inference(resolution,[status(thm)],[c_6,c_495])).

tff(c_521,plain,(
    ! [C_155] :
      ( k1_relset_1(k1_relat_1(C_155),k2_relat_1(C_155),C_155) = k10_relat_1(C_155,k2_relat_1(C_155))
      | ~ v1_relat_1(C_155)
      | ~ r1_tarski(k1_relat_1(C_155),k1_relat_1(C_155))
      | ~ v1_relat_1(C_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_499])).

tff(c_535,plain,(
    ! [C_156] :
      ( k1_relset_1(k1_relat_1(C_156),k2_relat_1(C_156),C_156) = k10_relat_1(C_156,k2_relat_1(C_156))
      | ~ v1_relat_1(C_156) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_521])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( k1_relset_1(A_6,B_7,C_8) = k1_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_452,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ r1_tarski(k2_relat_1(C_129),B_128)
      | ~ r1_tarski(k1_relat_1(C_129),A_127)
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_408,c_10])).

tff(c_457,plain,(
    ! [A_130,C_131] :
      ( k1_relset_1(A_130,k2_relat_1(C_131),C_131) = k1_relat_1(C_131)
      | ~ r1_tarski(k1_relat_1(C_131),A_130)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_452])).

tff(c_461,plain,(
    ! [C_131] :
      ( k1_relset_1(k1_relat_1(C_131),k2_relat_1(C_131),C_131) = k1_relat_1(C_131)
      | ~ v1_relat_1(C_131) ) ),
    inference(resolution,[status(thm)],[c_6,c_457])).

tff(c_550,plain,(
    ! [C_157] :
      ( k10_relat_1(C_157,k2_relat_1(C_157)) = k1_relat_1(C_157)
      | ~ v1_relat_1(C_157)
      | ~ v1_relat_1(C_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_535,c_461])).

tff(c_321,plain,(
    ! [A_102,B_103,C_104,D_105] :
      ( k7_relset_1(A_102,B_103,C_104,D_105) = k9_relat_1(C_104,D_105)
      | ~ m1_subset_1(C_104,k1_zfmisc_1(k2_zfmisc_1(A_102,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_324,plain,(
    ! [D_105] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_105) = k9_relat_1('#skF_3',D_105) ),
    inference(resolution,[status(thm)],[c_26,c_321])).

tff(c_41,plain,(
    ! [A_32,B_33,C_34] :
      ( k2_relset_1(A_32,B_33,C_34) = k2_relat_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_41])).

tff(c_398,plain,(
    ! [A_115,B_116,C_117] :
      ( k7_relset_1(A_115,B_116,C_117,A_115) = k2_relset_1(A_115,B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_400,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_398])).

tff(c_402,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_45,c_400])).

tff(c_346,plain,(
    ! [A_107,B_108,C_109,D_110] :
      ( k8_relset_1(A_107,B_108,C_109,D_110) = k10_relat_1(C_109,D_110)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_349,plain,(
    ! [D_110] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_110) = k10_relat_1('#skF_3',D_110) ),
    inference(resolution,[status(thm)],[c_26,c_346])).

tff(c_108,plain,(
    ! [C_54,A_55,B_56] :
      ( m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56)))
      | ~ r1_tarski(k2_relat_1(C_54),B_56)
      | ~ r1_tarski(k1_relat_1(C_54),A_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    ! [A_23,B_24,C_25] :
      ( k7_relset_1(A_23,B_24,C_25,A_23) = k2_relset_1(A_23,B_24,C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_259,plain,(
    ! [A_94,B_95,C_96] :
      ( k7_relset_1(A_94,B_95,C_96,A_94) = k2_relset_1(A_94,B_95,C_96)
      | ~ r1_tarski(k2_relat_1(C_96),B_95)
      | ~ r1_tarski(k1_relat_1(C_96),A_94)
      | ~ v1_relat_1(C_96) ) ),
    inference(resolution,[status(thm)],[c_108,c_22])).

tff(c_264,plain,(
    ! [A_97,C_98] :
      ( k7_relset_1(A_97,k2_relat_1(C_98),C_98,A_97) = k2_relset_1(A_97,k2_relat_1(C_98),C_98)
      | ~ r1_tarski(k1_relat_1(C_98),A_97)
      | ~ v1_relat_1(C_98) ) ),
    inference(resolution,[status(thm)],[c_6,c_259])).

tff(c_269,plain,(
    ! [C_99] :
      ( k7_relset_1(k1_relat_1(C_99),k2_relat_1(C_99),C_99,k1_relat_1(C_99)) = k2_relset_1(k1_relat_1(C_99),k2_relat_1(C_99),C_99)
      | ~ v1_relat_1(C_99) ) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( k7_relset_1(A_12,B_13,C_14,D_15) = k9_relat_1(C_14,D_15)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_12,B_13))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_190,plain,(
    ! [A_78,B_79,C_80,D_81] :
      ( k7_relset_1(A_78,B_79,C_80,D_81) = k9_relat_1(C_80,D_81)
      | ~ r1_tarski(k2_relat_1(C_80),B_79)
      | ~ r1_tarski(k1_relat_1(C_80),A_78)
      | ~ v1_relat_1(C_80) ) ),
    inference(resolution,[status(thm)],[c_108,c_14])).

tff(c_195,plain,(
    ! [A_82,C_83,D_84] :
      ( k7_relset_1(A_82,k2_relat_1(C_83),C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ r1_tarski(k1_relat_1(C_83),A_82)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_190])).

tff(c_199,plain,(
    ! [C_83,D_84] :
      ( k7_relset_1(k1_relat_1(C_83),k2_relat_1(C_83),C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ v1_relat_1(C_83) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_285,plain,(
    ! [C_100] :
      ( k2_relset_1(k1_relat_1(C_100),k2_relat_1(C_100),C_100) = k9_relat_1(C_100,k1_relat_1(C_100))
      | ~ v1_relat_1(C_100)
      | ~ v1_relat_1(C_100) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_199])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] :
      ( k2_relset_1(A_9,B_10,C_11) = k2_relat_1(C_11)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_143,plain,(
    ! [A_62,B_63,C_64] :
      ( k2_relset_1(A_62,B_63,C_64) = k2_relat_1(C_64)
      | ~ r1_tarski(k2_relat_1(C_64),B_63)
      | ~ r1_tarski(k1_relat_1(C_64),A_62)
      | ~ v1_relat_1(C_64) ) ),
    inference(resolution,[status(thm)],[c_108,c_12])).

tff(c_157,plain,(
    ! [A_66,C_67] :
      ( k2_relset_1(A_66,k2_relat_1(C_67),C_67) = k2_relat_1(C_67)
      | ~ r1_tarski(k1_relat_1(C_67),A_66)
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_143])).

tff(c_161,plain,(
    ! [C_67] :
      ( k2_relset_1(k1_relat_1(C_67),k2_relat_1(C_67),C_67) = k2_relat_1(C_67)
      | ~ v1_relat_1(C_67) ) ),
    inference(resolution,[status(thm)],[c_6,c_157])).

tff(c_300,plain,(
    ! [C_101] :
      ( k9_relat_1(C_101,k1_relat_1(C_101)) = k2_relat_1(C_101)
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(C_101)
      | ~ v1_relat_1(C_101) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_285,c_161])).

tff(c_75,plain,(
    ! [A_43,B_44,C_45,D_46] :
      ( k8_relset_1(A_43,B_44,C_45,D_46) = k10_relat_1(C_45,D_46)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_78,plain,(
    ! [D_46] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_46) = k10_relat_1('#skF_3',D_46) ),
    inference(resolution,[status(thm)],[c_26,c_75])).

tff(c_50,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_54,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_50])).

tff(c_98,plain,(
    ! [A_51,B_52,C_53] :
      ( k8_relset_1(A_51,B_52,C_53,B_52) = k1_relset_1(A_51,B_52,C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_100,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_102,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_54,c_100])).

tff(c_61,plain,(
    ! [A_38,B_39,C_40,D_41] :
      ( k7_relset_1(A_38,B_39,C_40,D_41) = k9_relat_1(C_40,D_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [D_41] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_41) = k9_relat_1('#skF_3',D_41) ),
    inference(resolution,[status(thm)],[c_26,c_61])).

tff(c_24,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_59,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_54,c_24])).

tff(c_60,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_65,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60])).

tff(c_88,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_65])).

tff(c_103,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_88])).

tff(c_306,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_103])).

tff(c_314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_306])).

tff(c_315,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_325,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_315])).

tff(c_377,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_325])).

tff(c_403,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_377])).

tff(c_556,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_403])).

tff(c_564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_556])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:51:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  
% 2.65/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.35  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.35  
% 2.65/1.35  %Foreground sorts:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Background operators:
% 2.65/1.35  
% 2.65/1.35  
% 2.65/1.35  %Foreground operators:
% 2.65/1.35  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.35  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.35  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.35  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.35  
% 2.82/1.37  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 2.82/1.37  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.82/1.37  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.82/1.37  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.82/1.37  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 2.82/1.37  tff(f_51, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.82/1.37  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.82/1.37  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.82/1.37  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.82/1.37  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.37  tff(c_29, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.82/1.37  tff(c_33, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.82/1.37  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.82/1.37  tff(c_408, plain, (![C_118, A_119, B_120]: (m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_120))) | ~r1_tarski(k2_relat_1(C_118), B_120) | ~r1_tarski(k1_relat_1(C_118), A_119) | ~v1_relat_1(C_118))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.37  tff(c_20, plain, (![A_23, B_24, C_25]: (k8_relset_1(A_23, B_24, C_25, B_24)=k1_relset_1(A_23, B_24, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.37  tff(c_509, plain, (![A_151, B_152, C_153]: (k8_relset_1(A_151, B_152, C_153, B_152)=k1_relset_1(A_151, B_152, C_153) | ~r1_tarski(k2_relat_1(C_153), B_152) | ~r1_tarski(k1_relat_1(C_153), A_151) | ~v1_relat_1(C_153))), inference(resolution, [status(thm)], [c_408, c_20])).
% 2.82/1.38  tff(c_514, plain, (![A_154, C_155]: (k8_relset_1(A_154, k2_relat_1(C_155), C_155, k2_relat_1(C_155))=k1_relset_1(A_154, k2_relat_1(C_155), C_155) | ~r1_tarski(k1_relat_1(C_155), A_154) | ~v1_relat_1(C_155))), inference(resolution, [status(thm)], [c_6, c_509])).
% 2.82/1.38  tff(c_16, plain, (![A_16, B_17, C_18, D_19]: (k8_relset_1(A_16, B_17, C_18, D_19)=k10_relat_1(C_18, D_19) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.38  tff(c_481, plain, (![A_140, B_141, C_142, D_143]: (k8_relset_1(A_140, B_141, C_142, D_143)=k10_relat_1(C_142, D_143) | ~r1_tarski(k2_relat_1(C_142), B_141) | ~r1_tarski(k1_relat_1(C_142), A_140) | ~v1_relat_1(C_142))), inference(resolution, [status(thm)], [c_408, c_16])).
% 2.82/1.38  tff(c_495, plain, (![A_146, C_147, D_148]: (k8_relset_1(A_146, k2_relat_1(C_147), C_147, D_148)=k10_relat_1(C_147, D_148) | ~r1_tarski(k1_relat_1(C_147), A_146) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_6, c_481])).
% 2.82/1.38  tff(c_499, plain, (![C_147, D_148]: (k8_relset_1(k1_relat_1(C_147), k2_relat_1(C_147), C_147, D_148)=k10_relat_1(C_147, D_148) | ~v1_relat_1(C_147))), inference(resolution, [status(thm)], [c_6, c_495])).
% 2.82/1.38  tff(c_521, plain, (![C_155]: (k1_relset_1(k1_relat_1(C_155), k2_relat_1(C_155), C_155)=k10_relat_1(C_155, k2_relat_1(C_155)) | ~v1_relat_1(C_155) | ~r1_tarski(k1_relat_1(C_155), k1_relat_1(C_155)) | ~v1_relat_1(C_155))), inference(superposition, [status(thm), theory('equality')], [c_514, c_499])).
% 2.82/1.38  tff(c_535, plain, (![C_156]: (k1_relset_1(k1_relat_1(C_156), k2_relat_1(C_156), C_156)=k10_relat_1(C_156, k2_relat_1(C_156)) | ~v1_relat_1(C_156))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_521])).
% 2.82/1.38  tff(c_10, plain, (![A_6, B_7, C_8]: (k1_relset_1(A_6, B_7, C_8)=k1_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.38  tff(c_452, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~r1_tarski(k2_relat_1(C_129), B_128) | ~r1_tarski(k1_relat_1(C_129), A_127) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_408, c_10])).
% 2.82/1.38  tff(c_457, plain, (![A_130, C_131]: (k1_relset_1(A_130, k2_relat_1(C_131), C_131)=k1_relat_1(C_131) | ~r1_tarski(k1_relat_1(C_131), A_130) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_6, c_452])).
% 2.82/1.38  tff(c_461, plain, (![C_131]: (k1_relset_1(k1_relat_1(C_131), k2_relat_1(C_131), C_131)=k1_relat_1(C_131) | ~v1_relat_1(C_131))), inference(resolution, [status(thm)], [c_6, c_457])).
% 2.82/1.38  tff(c_550, plain, (![C_157]: (k10_relat_1(C_157, k2_relat_1(C_157))=k1_relat_1(C_157) | ~v1_relat_1(C_157) | ~v1_relat_1(C_157))), inference(superposition, [status(thm), theory('equality')], [c_535, c_461])).
% 2.82/1.38  tff(c_321, plain, (![A_102, B_103, C_104, D_105]: (k7_relset_1(A_102, B_103, C_104, D_105)=k9_relat_1(C_104, D_105) | ~m1_subset_1(C_104, k1_zfmisc_1(k2_zfmisc_1(A_102, B_103))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.38  tff(c_324, plain, (![D_105]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_105)=k9_relat_1('#skF_3', D_105))), inference(resolution, [status(thm)], [c_26, c_321])).
% 2.82/1.38  tff(c_41, plain, (![A_32, B_33, C_34]: (k2_relset_1(A_32, B_33, C_34)=k2_relat_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.38  tff(c_45, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_41])).
% 2.82/1.38  tff(c_398, plain, (![A_115, B_116, C_117]: (k7_relset_1(A_115, B_116, C_117, A_115)=k2_relset_1(A_115, B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.38  tff(c_400, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_398])).
% 2.82/1.38  tff(c_402, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_45, c_400])).
% 2.82/1.38  tff(c_346, plain, (![A_107, B_108, C_109, D_110]: (k8_relset_1(A_107, B_108, C_109, D_110)=k10_relat_1(C_109, D_110) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.38  tff(c_349, plain, (![D_110]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_110)=k10_relat_1('#skF_3', D_110))), inference(resolution, [status(thm)], [c_26, c_346])).
% 2.82/1.38  tff(c_108, plain, (![C_54, A_55, B_56]: (m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))) | ~r1_tarski(k2_relat_1(C_54), B_56) | ~r1_tarski(k1_relat_1(C_54), A_55) | ~v1_relat_1(C_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.82/1.38  tff(c_22, plain, (![A_23, B_24, C_25]: (k7_relset_1(A_23, B_24, C_25, A_23)=k2_relset_1(A_23, B_24, C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.38  tff(c_259, plain, (![A_94, B_95, C_96]: (k7_relset_1(A_94, B_95, C_96, A_94)=k2_relset_1(A_94, B_95, C_96) | ~r1_tarski(k2_relat_1(C_96), B_95) | ~r1_tarski(k1_relat_1(C_96), A_94) | ~v1_relat_1(C_96))), inference(resolution, [status(thm)], [c_108, c_22])).
% 2.82/1.38  tff(c_264, plain, (![A_97, C_98]: (k7_relset_1(A_97, k2_relat_1(C_98), C_98, A_97)=k2_relset_1(A_97, k2_relat_1(C_98), C_98) | ~r1_tarski(k1_relat_1(C_98), A_97) | ~v1_relat_1(C_98))), inference(resolution, [status(thm)], [c_6, c_259])).
% 2.82/1.38  tff(c_269, plain, (![C_99]: (k7_relset_1(k1_relat_1(C_99), k2_relat_1(C_99), C_99, k1_relat_1(C_99))=k2_relset_1(k1_relat_1(C_99), k2_relat_1(C_99), C_99) | ~v1_relat_1(C_99))), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.82/1.38  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k7_relset_1(A_12, B_13, C_14, D_15)=k9_relat_1(C_14, D_15) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_12, B_13))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.38  tff(c_190, plain, (![A_78, B_79, C_80, D_81]: (k7_relset_1(A_78, B_79, C_80, D_81)=k9_relat_1(C_80, D_81) | ~r1_tarski(k2_relat_1(C_80), B_79) | ~r1_tarski(k1_relat_1(C_80), A_78) | ~v1_relat_1(C_80))), inference(resolution, [status(thm)], [c_108, c_14])).
% 2.82/1.38  tff(c_195, plain, (![A_82, C_83, D_84]: (k7_relset_1(A_82, k2_relat_1(C_83), C_83, D_84)=k9_relat_1(C_83, D_84) | ~r1_tarski(k1_relat_1(C_83), A_82) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_6, c_190])).
% 2.82/1.38  tff(c_199, plain, (![C_83, D_84]: (k7_relset_1(k1_relat_1(C_83), k2_relat_1(C_83), C_83, D_84)=k9_relat_1(C_83, D_84) | ~v1_relat_1(C_83))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.82/1.38  tff(c_285, plain, (![C_100]: (k2_relset_1(k1_relat_1(C_100), k2_relat_1(C_100), C_100)=k9_relat_1(C_100, k1_relat_1(C_100)) | ~v1_relat_1(C_100) | ~v1_relat_1(C_100))), inference(superposition, [status(thm), theory('equality')], [c_269, c_199])).
% 2.82/1.38  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_relset_1(A_9, B_10, C_11)=k2_relat_1(C_11) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.82/1.38  tff(c_143, plain, (![A_62, B_63, C_64]: (k2_relset_1(A_62, B_63, C_64)=k2_relat_1(C_64) | ~r1_tarski(k2_relat_1(C_64), B_63) | ~r1_tarski(k1_relat_1(C_64), A_62) | ~v1_relat_1(C_64))), inference(resolution, [status(thm)], [c_108, c_12])).
% 2.82/1.38  tff(c_157, plain, (![A_66, C_67]: (k2_relset_1(A_66, k2_relat_1(C_67), C_67)=k2_relat_1(C_67) | ~r1_tarski(k1_relat_1(C_67), A_66) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_6, c_143])).
% 2.82/1.38  tff(c_161, plain, (![C_67]: (k2_relset_1(k1_relat_1(C_67), k2_relat_1(C_67), C_67)=k2_relat_1(C_67) | ~v1_relat_1(C_67))), inference(resolution, [status(thm)], [c_6, c_157])).
% 2.82/1.38  tff(c_300, plain, (![C_101]: (k9_relat_1(C_101, k1_relat_1(C_101))=k2_relat_1(C_101) | ~v1_relat_1(C_101) | ~v1_relat_1(C_101) | ~v1_relat_1(C_101))), inference(superposition, [status(thm), theory('equality')], [c_285, c_161])).
% 2.82/1.38  tff(c_75, plain, (![A_43, B_44, C_45, D_46]: (k8_relset_1(A_43, B_44, C_45, D_46)=k10_relat_1(C_45, D_46) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.82/1.38  tff(c_78, plain, (![D_46]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_46)=k10_relat_1('#skF_3', D_46))), inference(resolution, [status(thm)], [c_26, c_75])).
% 2.82/1.38  tff(c_50, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.82/1.38  tff(c_54, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_50])).
% 2.82/1.38  tff(c_98, plain, (![A_51, B_52, C_53]: (k8_relset_1(A_51, B_52, C_53, B_52)=k1_relset_1(A_51, B_52, C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.82/1.38  tff(c_100, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_98])).
% 2.82/1.38  tff(c_102, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_54, c_100])).
% 2.82/1.38  tff(c_61, plain, (![A_38, B_39, C_40, D_41]: (k7_relset_1(A_38, B_39, C_40, D_41)=k9_relat_1(C_40, D_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.82/1.38  tff(c_64, plain, (![D_41]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_41)=k9_relat_1('#skF_3', D_41))), inference(resolution, [status(thm)], [c_26, c_61])).
% 2.82/1.38  tff(c_24, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.82/1.38  tff(c_59, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_45, c_54, c_24])).
% 2.82/1.38  tff(c_60, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_59])).
% 2.82/1.38  tff(c_65, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60])).
% 2.82/1.38  tff(c_88, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_65])).
% 2.82/1.38  tff(c_103, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_88])).
% 2.82/1.38  tff(c_306, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_300, c_103])).
% 2.82/1.38  tff(c_314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_306])).
% 2.82/1.38  tff(c_315, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_59])).
% 2.82/1.38  tff(c_325, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_315])).
% 2.82/1.38  tff(c_377, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_349, c_325])).
% 2.82/1.38  tff(c_403, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_402, c_377])).
% 2.82/1.38  tff(c_556, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_550, c_403])).
% 2.82/1.38  tff(c_564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_556])).
% 2.82/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.82/1.38  
% 2.82/1.38  Inference rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Ref     : 0
% 2.82/1.38  #Sup     : 130
% 2.82/1.38  #Fact    : 0
% 2.82/1.38  #Define  : 0
% 2.82/1.38  #Split   : 1
% 2.82/1.38  #Chain   : 0
% 2.82/1.38  #Close   : 0
% 2.82/1.38  
% 2.82/1.38  Ordering : KBO
% 2.82/1.38  
% 2.82/1.38  Simplification rules
% 2.82/1.38  ----------------------
% 2.82/1.38  #Subsume      : 3
% 2.82/1.38  #Demod        : 29
% 2.82/1.38  #Tautology    : 70
% 2.82/1.38  #SimpNegUnit  : 0
% 2.82/1.38  #BackRed      : 8
% 2.82/1.38  
% 2.82/1.38  #Partial instantiations: 0
% 2.82/1.38  #Strategies tried      : 1
% 2.82/1.38  
% 2.82/1.38  Timing (in seconds)
% 2.82/1.38  ----------------------
% 2.82/1.38  Preprocessing        : 0.30
% 2.82/1.38  Parsing              : 0.16
% 2.82/1.38  CNF conversion       : 0.02
% 2.82/1.38  Main loop            : 0.30
% 2.82/1.38  Inferencing          : 0.12
% 2.82/1.38  Reduction            : 0.08
% 2.82/1.38  Demodulation         : 0.06
% 2.82/1.38  BG Simplification    : 0.02
% 2.82/1.38  Subsumption          : 0.05
% 2.82/1.38  Abstraction          : 0.02
% 2.82/1.38  MUC search           : 0.00
% 2.82/1.38  Cooper               : 0.00
% 2.82/1.38  Total                : 0.64
% 2.82/1.38  Index Insertion      : 0.00
% 2.82/1.38  Index Deletion       : 0.00
% 2.82/1.38  Index Matching       : 0.00
% 2.82/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
