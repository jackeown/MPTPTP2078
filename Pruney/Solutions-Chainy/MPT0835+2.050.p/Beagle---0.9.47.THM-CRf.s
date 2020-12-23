%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:02 EST 2020

% Result     : Theorem 3.20s
% Output     : CNFRefutation 3.29s
% Verified   : 
% Statistics : Number of formulae       :   79 ( 182 expanded)
%              Number of leaves         :   27 (  76 expanded)
%              Depth                    :    7
%              Number of atoms          :  102 ( 312 expanded)
%              Number of equality atoms :   55 ( 148 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_43,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C)
        & k8_relset_1(A,B,C,B) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_281,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k7_relset_1(A_81,B_82,C_83,D_84) = k9_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_284,plain,(
    ! [D_84] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_84) = k9_relat_1('#skF_3',D_84) ),
    inference(resolution,[status(thm)],[c_26,c_281])).

tff(c_36,plain,(
    ! [A_31,B_32,C_33] :
      ( k2_relset_1(A_31,B_32,C_33) = k2_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_40,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_36])).

tff(c_329,plain,(
    ! [A_89,B_90,C_91] :
      ( k7_relset_1(A_89,B_90,C_91,A_89) = k2_relset_1(A_89,B_90,C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_331,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2') = k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_329])).

tff(c_333,plain,(
    k9_relat_1('#skF_3','#skF_2') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_40,c_331])).

tff(c_54,plain,(
    ! [A_37,B_38,C_39,D_40] :
      ( k8_relset_1(A_37,B_38,C_39,D_40) = k10_relat_1(C_39,D_40)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [D_40] : k8_relset_1('#skF_2','#skF_1','#skF_3',D_40) = k10_relat_1('#skF_3',D_40) ),
    inference(resolution,[status(thm)],[c_26,c_54])).

tff(c_45,plain,(
    ! [A_34,B_35,C_36] :
      ( k1_relset_1(A_34,B_35,C_36) = k1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    k1_relset_1('#skF_2','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_45])).

tff(c_83,plain,(
    ! [A_47,B_48,C_49] :
      ( k8_relset_1(A_47,B_48,C_49,B_48) = k1_relset_1(A_47,B_48,C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_85,plain,(
    k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1') = k1_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_83])).

tff(c_87,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_49,c_85])).

tff(c_69,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k7_relset_1(A_42,B_43,C_44,D_45) = k9_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_72,plain,(
    ! [D_45] : k7_relset_1('#skF_2','#skF_1','#skF_3',D_45) = k9_relat_1('#skF_3',D_45) ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_24,plain,
    ( k8_relset_1('#skF_2','#skF_1','#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relset_1('#skF_2','#skF_1','#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k8_relset_1('#skF_2','#skF_1','#skF_3','#skF_1')) != k2_relset_1('#skF_2','#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_67,plain,
    ( k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3')
    | k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_40,c_57,c_49,c_24])).

tff(c_68,plain,(
    k7_relset_1('#skF_2','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_67])).

tff(c_73,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68])).

tff(c_93,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [D_60,B_61,C_62,A_63] :
      ( m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(B_61,C_62)))
      | ~ r1_tarski(k1_relat_1(D_60),B_61)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_63,C_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_157,plain,(
    ! [B_64] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(B_64,'#skF_1')))
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_64) ) ),
    inference(resolution,[status(thm)],[c_26,c_150])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( k7_relset_1(A_9,B_10,C_11,D_12) = k9_relat_1(C_11,D_12)
      | ~ m1_subset_1(C_11,k1_zfmisc_1(k2_zfmisc_1(A_9,B_10))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_218,plain,(
    ! [B_70,D_71] :
      ( k7_relset_1(B_70,'#skF_1','#skF_3',D_71) = k9_relat_1('#skF_3',D_71)
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_70) ) ),
    inference(resolution,[status(thm)],[c_157,c_12])).

tff(c_222,plain,(
    ! [D_71] : k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',D_71) = k9_relat_1('#skF_3',D_71) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_10,plain,(
    ! [A_6,B_7,C_8] :
      ( k2_relset_1(A_6,B_7,C_8) = k2_relat_1(C_8)
      | ~ m1_subset_1(C_8,k1_zfmisc_1(k2_zfmisc_1(A_6,B_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_194,plain,(
    ! [B_66] :
      ( k2_relset_1(B_66,'#skF_1','#skF_3') = k2_relat_1('#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_66) ) ),
    inference(resolution,[status(thm)],[c_157,c_10])).

tff(c_199,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_194])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( k7_relset_1(A_25,B_26,C_27,A_25) = k2_relset_1(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_267,plain,(
    ! [B_80] :
      ( k7_relset_1(B_80,'#skF_1','#skF_3',B_80) = k2_relset_1(B_80,'#skF_1','#skF_3')
      | ~ r1_tarski(k1_relat_1('#skF_3'),B_80) ) ),
    inference(resolution,[status(thm)],[c_157,c_22])).

tff(c_270,plain,(
    k7_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3',k1_relat_1('#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_267])).

tff(c_272,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_199,c_270])).

tff(c_274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_93,c_272])).

tff(c_275,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_2','#skF_1','#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_67])).

tff(c_285,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_275])).

tff(c_334,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_285])).

tff(c_343,plain,(
    ! [D_96,C_97,B_98,A_99] :
      ( m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(C_97,B_98)))
      | ~ r1_tarski(k2_relat_1(D_96),B_98)
      | ~ m1_subset_1(D_96,k1_zfmisc_1(k2_zfmisc_1(C_97,A_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_374,plain,(
    ! [B_101] :
      ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_2',B_101)))
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_101) ) ),
    inference(resolution,[status(thm)],[c_26,c_343])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( k8_relset_1(A_13,B_14,C_15,D_16) = k10_relat_1(C_15,D_16)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_483,plain,(
    ! [B_115,D_116] :
      ( k8_relset_1('#skF_2',B_115,'#skF_3',D_116) = k10_relat_1('#skF_3',D_116)
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_115) ) ),
    inference(resolution,[status(thm)],[c_374,c_14])).

tff(c_487,plain,(
    ! [D_116] : k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',D_116) = k10_relat_1('#skF_3',D_116) ),
    inference(resolution,[status(thm)],[c_6,c_483])).

tff(c_8,plain,(
    ! [A_3,B_4,C_5] :
      ( k1_relset_1(A_3,B_4,C_5) = k1_relat_1(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(A_3,B_4))) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_431,plain,(
    ! [B_105] :
      ( k1_relset_1('#skF_2',B_105,'#skF_3') = k1_relat_1('#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_105) ) ),
    inference(resolution,[status(thm)],[c_374,c_8])).

tff(c_436,plain,(
    k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_431])).

tff(c_20,plain,(
    ! [A_25,B_26,C_27] :
      ( k8_relset_1(A_25,B_26,C_27,B_26) = k1_relset_1(A_25,B_26,C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_497,plain,(
    ! [B_118] :
      ( k8_relset_1('#skF_2',B_118,'#skF_3',B_118) = k1_relset_1('#skF_2',B_118,'#skF_3')
      | ~ r1_tarski(k2_relat_1('#skF_3'),B_118) ) ),
    inference(resolution,[status(thm)],[c_374,c_20])).

tff(c_500,plain,(
    k8_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3',k2_relat_1('#skF_3')) = k1_relset_1('#skF_2',k2_relat_1('#skF_3'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_497])).

tff(c_502,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_436,c_500])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_334,c_502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:20:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.20/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.83  
% 3.20/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.20/1.84  %$ r1_tarski > m1_subset_1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.20/1.84  
% 3.20/1.84  %Foreground sorts:
% 3.20/1.84  
% 3.20/1.84  
% 3.20/1.84  %Background operators:
% 3.20/1.84  
% 3.20/1.84  
% 3.20/1.84  %Foreground operators:
% 3.20/1.84  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 3.20/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.20/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.20/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.20/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 3.20/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.20/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.20/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.20/1.84  tff('#skF_1', type, '#skF_1': $i).
% 3.20/1.84  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.20/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.20/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.20/1.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.20/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.20/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.20/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.20/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.20/1.84  
% 3.29/1.86  tff(f_72, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => ((k7_relset_1(B, A, C, k8_relset_1(B, A, C, A)) = k2_relset_1(B, A, C)) & (k8_relset_1(B, A, C, k7_relset_1(B, A, C, B)) = k1_relset_1(B, A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_relset_1)).
% 3.29/1.86  tff(f_43, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 3.29/1.86  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 3.29/1.86  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C)) & (k8_relset_1(A, B, C, B) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_relset_1)).
% 3.29/1.86  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 3.29/1.86  tff(f_35, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.29/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.29/1.86  tff(f_53, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_relset_1)).
% 3.29/1.86  tff(f_59, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_relset_1)).
% 3.29/1.86  tff(c_26, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.29/1.86  tff(c_281, plain, (![A_81, B_82, C_83, D_84]: (k7_relset_1(A_81, B_82, C_83, D_84)=k9_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.86  tff(c_284, plain, (![D_84]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_84)=k9_relat_1('#skF_3', D_84))), inference(resolution, [status(thm)], [c_26, c_281])).
% 3.29/1.86  tff(c_36, plain, (![A_31, B_32, C_33]: (k2_relset_1(A_31, B_32, C_33)=k2_relat_1(C_33) | ~m1_subset_1(C_33, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.86  tff(c_40, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_36])).
% 3.29/1.86  tff(c_329, plain, (![A_89, B_90, C_91]: (k7_relset_1(A_89, B_90, C_91, A_89)=k2_relset_1(A_89, B_90, C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.86  tff(c_331, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2')=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_329])).
% 3.29/1.86  tff(c_333, plain, (k9_relat_1('#skF_3', '#skF_2')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_40, c_331])).
% 3.29/1.86  tff(c_54, plain, (![A_37, B_38, C_39, D_40]: (k8_relset_1(A_37, B_38, C_39, D_40)=k10_relat_1(C_39, D_40) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.86  tff(c_57, plain, (![D_40]: (k8_relset_1('#skF_2', '#skF_1', '#skF_3', D_40)=k10_relat_1('#skF_3', D_40))), inference(resolution, [status(thm)], [c_26, c_54])).
% 3.29/1.86  tff(c_45, plain, (![A_34, B_35, C_36]: (k1_relset_1(A_34, B_35, C_36)=k1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.86  tff(c_49, plain, (k1_relset_1('#skF_2', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26, c_45])).
% 3.29/1.86  tff(c_83, plain, (![A_47, B_48, C_49]: (k8_relset_1(A_47, B_48, C_49, B_48)=k1_relset_1(A_47, B_48, C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.86  tff(c_85, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1')=k1_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_83])).
% 3.29/1.86  tff(c_87, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_49, c_85])).
% 3.29/1.86  tff(c_69, plain, (![A_42, B_43, C_44, D_45]: (k7_relset_1(A_42, B_43, C_44, D_45)=k9_relat_1(C_44, D_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.86  tff(c_72, plain, (![D_45]: (k7_relset_1('#skF_2', '#skF_1', '#skF_3', D_45)=k9_relat_1('#skF_3', D_45))), inference(resolution, [status(thm)], [c_26, c_69])).
% 3.29/1.86  tff(c_24, plain, (k8_relset_1('#skF_2', '#skF_1', '#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relset_1('#skF_2', '#skF_1', '#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k8_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_1'))!=k2_relset_1('#skF_2', '#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.29/1.86  tff(c_67, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3') | k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_57, c_40, c_57, c_49, c_24])).
% 3.29/1.86  tff(c_68, plain, (k7_relset_1('#skF_2', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_67])).
% 3.29/1.86  tff(c_73, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_68])).
% 3.29/1.86  tff(c_93, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_87, c_73])).
% 3.29/1.86  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.29/1.86  tff(c_150, plain, (![D_60, B_61, C_62, A_63]: (m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(B_61, C_62))) | ~r1_tarski(k1_relat_1(D_60), B_61) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_63, C_62))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.29/1.86  tff(c_157, plain, (![B_64]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(B_64, '#skF_1'))) | ~r1_tarski(k1_relat_1('#skF_3'), B_64))), inference(resolution, [status(thm)], [c_26, c_150])).
% 3.29/1.86  tff(c_12, plain, (![A_9, B_10, C_11, D_12]: (k7_relset_1(A_9, B_10, C_11, D_12)=k9_relat_1(C_11, D_12) | ~m1_subset_1(C_11, k1_zfmisc_1(k2_zfmisc_1(A_9, B_10))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.29/1.86  tff(c_218, plain, (![B_70, D_71]: (k7_relset_1(B_70, '#skF_1', '#skF_3', D_71)=k9_relat_1('#skF_3', D_71) | ~r1_tarski(k1_relat_1('#skF_3'), B_70))), inference(resolution, [status(thm)], [c_157, c_12])).
% 3.29/1.86  tff(c_222, plain, (![D_71]: (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', D_71)=k9_relat_1('#skF_3', D_71))), inference(resolution, [status(thm)], [c_6, c_218])).
% 3.29/1.86  tff(c_10, plain, (![A_6, B_7, C_8]: (k2_relset_1(A_6, B_7, C_8)=k2_relat_1(C_8) | ~m1_subset_1(C_8, k1_zfmisc_1(k2_zfmisc_1(A_6, B_7))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.29/1.86  tff(c_194, plain, (![B_66]: (k2_relset_1(B_66, '#skF_1', '#skF_3')=k2_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_66))), inference(resolution, [status(thm)], [c_157, c_10])).
% 3.29/1.86  tff(c_199, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_194])).
% 3.29/1.86  tff(c_22, plain, (![A_25, B_26, C_27]: (k7_relset_1(A_25, B_26, C_27, A_25)=k2_relset_1(A_25, B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.86  tff(c_267, plain, (![B_80]: (k7_relset_1(B_80, '#skF_1', '#skF_3', B_80)=k2_relset_1(B_80, '#skF_1', '#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), B_80))), inference(resolution, [status(thm)], [c_157, c_22])).
% 3.29/1.86  tff(c_270, plain, (k7_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3', k1_relat_1('#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_6, c_267])).
% 3.29/1.86  tff(c_272, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_199, c_270])).
% 3.29/1.86  tff(c_274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_93, c_272])).
% 3.29/1.86  tff(c_275, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_2', '#skF_1', '#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_67])).
% 3.29/1.86  tff(c_285, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_275])).
% 3.29/1.86  tff(c_334, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_333, c_285])).
% 3.29/1.86  tff(c_343, plain, (![D_96, C_97, B_98, A_99]: (m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(C_97, B_98))) | ~r1_tarski(k2_relat_1(D_96), B_98) | ~m1_subset_1(D_96, k1_zfmisc_1(k2_zfmisc_1(C_97, A_99))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.29/1.86  tff(c_374, plain, (![B_101]: (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_2', B_101))) | ~r1_tarski(k2_relat_1('#skF_3'), B_101))), inference(resolution, [status(thm)], [c_26, c_343])).
% 3.29/1.86  tff(c_14, plain, (![A_13, B_14, C_15, D_16]: (k8_relset_1(A_13, B_14, C_15, D_16)=k10_relat_1(C_15, D_16) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.29/1.86  tff(c_483, plain, (![B_115, D_116]: (k8_relset_1('#skF_2', B_115, '#skF_3', D_116)=k10_relat_1('#skF_3', D_116) | ~r1_tarski(k2_relat_1('#skF_3'), B_115))), inference(resolution, [status(thm)], [c_374, c_14])).
% 3.29/1.86  tff(c_487, plain, (![D_116]: (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', D_116)=k10_relat_1('#skF_3', D_116))), inference(resolution, [status(thm)], [c_6, c_483])).
% 3.29/1.86  tff(c_8, plain, (![A_3, B_4, C_5]: (k1_relset_1(A_3, B_4, C_5)=k1_relat_1(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(A_3, B_4))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.29/1.86  tff(c_431, plain, (![B_105]: (k1_relset_1('#skF_2', B_105, '#skF_3')=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_105))), inference(resolution, [status(thm)], [c_374, c_8])).
% 3.29/1.86  tff(c_436, plain, (k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_431])).
% 3.29/1.86  tff(c_20, plain, (![A_25, B_26, C_27]: (k8_relset_1(A_25, B_26, C_27, B_26)=k1_relset_1(A_25, B_26, C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.29/1.86  tff(c_497, plain, (![B_118]: (k8_relset_1('#skF_2', B_118, '#skF_3', B_118)=k1_relset_1('#skF_2', B_118, '#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), B_118))), inference(resolution, [status(thm)], [c_374, c_20])).
% 3.29/1.86  tff(c_500, plain, (k8_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3', k2_relat_1('#skF_3'))=k1_relset_1('#skF_2', k2_relat_1('#skF_3'), '#skF_3')), inference(resolution, [status(thm)], [c_6, c_497])).
% 3.29/1.86  tff(c_502, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_436, c_500])).
% 3.29/1.86  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_334, c_502])).
% 3.29/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.29/1.86  
% 3.29/1.86  Inference rules
% 3.29/1.86  ----------------------
% 3.29/1.86  #Ref     : 0
% 3.29/1.86  #Sup     : 125
% 3.29/1.86  #Fact    : 0
% 3.29/1.86  #Define  : 0
% 3.29/1.86  #Split   : 1
% 3.29/1.86  #Chain   : 0
% 3.29/1.87  #Close   : 0
% 3.29/1.87  
% 3.29/1.87  Ordering : KBO
% 3.29/1.87  
% 3.29/1.87  Simplification rules
% 3.29/1.87  ----------------------
% 3.29/1.87  #Subsume      : 4
% 3.29/1.87  #Demod        : 31
% 3.29/1.87  #Tautology    : 62
% 3.29/1.87  #SimpNegUnit  : 2
% 3.29/1.87  #BackRed      : 5
% 3.29/1.87  
% 3.29/1.87  #Partial instantiations: 0
% 3.29/1.87  #Strategies tried      : 1
% 3.29/1.87  
% 3.29/1.87  Timing (in seconds)
% 3.29/1.87  ----------------------
% 3.29/1.87  Preprocessing        : 0.49
% 3.29/1.87  Parsing              : 0.25
% 3.29/1.87  CNF conversion       : 0.03
% 3.29/1.87  Main loop            : 0.47
% 3.29/1.87  Inferencing          : 0.17
% 3.29/1.87  Reduction            : 0.15
% 3.29/1.87  Demodulation         : 0.11
% 3.29/1.87  BG Simplification    : 0.03
% 3.29/1.87  Subsumption          : 0.08
% 3.29/1.87  Abstraction          : 0.03
% 3.29/1.87  MUC search           : 0.00
% 3.29/1.87  Cooper               : 0.00
% 3.29/1.87  Total                : 1.02
% 3.29/1.87  Index Insertion      : 0.00
% 3.29/1.87  Index Deletion       : 0.00
% 3.29/1.87  Index Matching       : 0.00
% 3.29/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
