%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:11 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 294 expanded)
%              Number of leaves         :   32 ( 110 expanded)
%              Depth                    :   13
%              Number of atoms          :  153 ( 649 expanded)
%              Number of equality atoms :   26 ( 139 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( ~ v1_xboole_0(B)
           => ! [C] :
                ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
               => ~ ( k1_relset_1(A,B,C) != k1_xboole_0
                    & ! [D] :
                        ( m1_subset_1(D,B)
                       => ~ r2_hidden(D,k2_relset_1(A,B,C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_79,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_88,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_79])).

tff(c_46,plain,(
    ! [C_42,A_43,B_44] :
      ( v1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_46])).

tff(c_12,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_122,plain,(
    ! [A_65,C_66,B_67] :
      ( m1_subset_1(A_65,C_66)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(C_66))
      | ~ r2_hidden(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_69,B_70,A_71] :
      ( m1_subset_1(A_69,B_70)
      | ~ r2_hidden(A_69,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_167,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1('#skF_1'(A_78),B_79)
      | ~ r1_tarski(A_78,B_79)
      | k1_xboole_0 = A_78 ) ),
    inference(resolution,[status(thm)],[c_2,c_130])).

tff(c_134,plain,(
    ! [A_72,B_73,C_74] :
      ( k2_relset_1(A_72,B_73,C_74) = k2_relat_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_143,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_56,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_61,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4')
    | k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_56])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_3','#skF_4','#skF_5')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_61])).

tff(c_144,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_5')),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_110])).

tff(c_194,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4')
    | k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_167,c_144])).

tff(c_201,plain,(
    ~ r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_194])).

tff(c_204,plain,
    ( ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_88,c_204])).

tff(c_209,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_210,plain,(
    r1_tarski(k2_relat_1('#skF_5'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_194])).

tff(c_233,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_210])).

tff(c_234,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_248,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_234])).

tff(c_28,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_260,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_28])).

tff(c_14,plain,(
    ! [A_10,B_11] :
      ( r2_hidden('#skF_2'(A_10,B_11),k2_relat_1(B_11))
      | ~ r2_hidden(A_10,k1_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_217,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_10,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_14])).

tff(c_301,plain,(
    ! [A_90] :
      ( r2_hidden('#skF_2'(A_90,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_90,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_217])).

tff(c_127,plain,(
    ! [A_65,B_4,A_3] :
      ( m1_subset_1(A_65,B_4)
      | ~ r2_hidden(A_65,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_338,plain,(
    ! [A_96,B_97] :
      ( m1_subset_1('#skF_2'(A_96,'#skF_5'),B_97)
      | ~ r1_tarski(k1_xboole_0,B_97)
      | ~ r2_hidden(A_96,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_301,c_127])).

tff(c_341,plain,(
    ! [B_97] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_97)
      | ~ r1_tarski(k1_xboole_0,B_97)
      | k1_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_338])).

tff(c_345,plain,(
    ! [B_98] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_98)
      | ~ r1_tarski(k1_xboole_0,B_98) ) ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_341])).

tff(c_156,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77),k2_relat_1(B_77))
      | ~ r2_hidden(A_76,k1_relat_1(B_77))
      | ~ v1_relat_1(B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_26,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k2_relset_1('#skF_3','#skF_4','#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_145,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k2_relat_1('#skF_5'))
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_26])).

tff(c_160,plain,(
    ! [A_76] :
      ( ~ m1_subset_1('#skF_2'(A_76,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_76,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_145])).

tff(c_282,plain,(
    ! [A_86] :
      ( ~ m1_subset_1('#skF_2'(A_86,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_86,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_160])).

tff(c_286,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_282])).

tff(c_289,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_286])).

tff(c_348,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_345,c_289])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_348])).

tff(c_380,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_61])).

tff(c_513,plain,(
    ! [A_134,B_135,C_136] :
      ( k2_relset_1(A_134,B_135,C_136) = k2_relat_1(C_136)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_524,plain,(
    k2_relset_1('#skF_3','#skF_4','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_513])).

tff(c_528,plain,(
    k2_relat_1('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_524])).

tff(c_538,plain,(
    ! [A_8] :
      ( r1_tarski(k1_xboole_0,A_8)
      | ~ v5_relat_1('#skF_5',A_8)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_12])).

tff(c_569,plain,(
    ! [A_138] :
      ( r1_tarski(k1_xboole_0,A_138)
      | ~ v5_relat_1('#skF_5',A_138) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_538])).

tff(c_577,plain,(
    r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_88,c_569])).

tff(c_443,plain,(
    ! [A_112,B_113,C_114] :
      ( k1_relset_1(A_112,B_113,C_114) = k1_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_457,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_443])).

tff(c_458,plain,(
    k1_relat_1('#skF_5') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_28])).

tff(c_532,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_10,k1_relat_1('#skF_5'))
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_14])).

tff(c_578,plain,(
    ! [A_139] :
      ( r2_hidden('#skF_2'(A_139,'#skF_5'),k1_xboole_0)
      | ~ r2_hidden(A_139,k1_relat_1('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_532])).

tff(c_406,plain,(
    ! [A_103,C_104,B_105] :
      ( m1_subset_1(A_103,C_104)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(C_104))
      | ~ r2_hidden(A_103,B_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_411,plain,(
    ! [A_103,B_4,A_3] :
      ( m1_subset_1(A_103,B_4)
      | ~ r2_hidden(A_103,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_406])).

tff(c_610,plain,(
    ! [A_144,B_145] :
      ( m1_subset_1('#skF_2'(A_144,'#skF_5'),B_145)
      | ~ r1_tarski(k1_xboole_0,B_145)
      | ~ r2_hidden(A_144,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_578,c_411])).

tff(c_613,plain,(
    ! [B_145] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_145)
      | ~ r1_tarski(k1_xboole_0,B_145)
      | k1_relat_1('#skF_5') = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_610])).

tff(c_617,plain,(
    ! [B_146] :
      ( m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),B_146)
      | ~ r1_tarski(k1_xboole_0,B_146) ) ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_613])).

tff(c_382,plain,(
    ! [D_36] :
      ( ~ r2_hidden(D_36,k1_xboole_0)
      | ~ m1_subset_1(D_36,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_26])).

tff(c_602,plain,(
    ! [A_143] :
      ( ~ m1_subset_1('#skF_2'(A_143,'#skF_5'),'#skF_4')
      | ~ r2_hidden(A_143,k1_relat_1('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_578,c_382])).

tff(c_606,plain,
    ( ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4')
    | k1_relat_1('#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_602])).

tff(c_609,plain,(
    ~ m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')),'#skF_5'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_458,c_606])).

tff(c_620,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(resolution,[status(thm)],[c_617,c_609])).

tff(c_651,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_577,c_620])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:08:30 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.33  
% 2.47/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.34  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.47/1.34  
% 2.47/1.34  %Foreground sorts:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Background operators:
% 2.47/1.34  
% 2.47/1.34  
% 2.47/1.34  %Foreground operators:
% 2.47/1.34  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.34  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.47/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.47/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.47/1.34  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.47/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.47/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.47/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.34  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.34  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.47/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.47/1.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.47/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.47/1.34  
% 2.84/1.36  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_relset_1)).
% 2.84/1.36  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.84/1.36  tff(f_62, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.84/1.36  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.84/1.36  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.84/1.36  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.84/1.36  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset)).
% 2.84/1.36  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.84/1.36  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.84/1.36  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 2.84/1.36  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.84/1.36  tff(c_79, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.84/1.36  tff(c_88, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_79])).
% 2.84/1.36  tff(c_46, plain, (![C_42, A_43, B_44]: (v1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.84/1.36  tff(c_55, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_46])).
% 2.84/1.36  tff(c_12, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.36  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.36  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.36  tff(c_122, plain, (![A_65, C_66, B_67]: (m1_subset_1(A_65, C_66) | ~m1_subset_1(B_67, k1_zfmisc_1(C_66)) | ~r2_hidden(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.36  tff(c_130, plain, (![A_69, B_70, A_71]: (m1_subset_1(A_69, B_70) | ~r2_hidden(A_69, A_71) | ~r1_tarski(A_71, B_70))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.84/1.36  tff(c_167, plain, (![A_78, B_79]: (m1_subset_1('#skF_1'(A_78), B_79) | ~r1_tarski(A_78, B_79) | k1_xboole_0=A_78)), inference(resolution, [status(thm)], [c_2, c_130])).
% 2.84/1.36  tff(c_134, plain, (![A_72, B_73, C_74]: (k2_relset_1(A_72, B_73, C_74)=k2_relat_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.36  tff(c_143, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.84/1.36  tff(c_56, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.84/1.36  tff(c_61, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4') | k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_56])).
% 2.84/1.36  tff(c_110, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_3', '#skF_4', '#skF_5')), '#skF_4')), inference(splitLeft, [status(thm)], [c_61])).
% 2.84/1.36  tff(c_144, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_5')), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_143, c_110])).
% 2.84/1.36  tff(c_194, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4') | k2_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_167, c_144])).
% 2.84/1.36  tff(c_201, plain, (~r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitLeft, [status(thm)], [c_194])).
% 2.84/1.36  tff(c_204, plain, (~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_12, c_201])).
% 2.84/1.36  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_55, c_88, c_204])).
% 2.84/1.36  tff(c_209, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_194])).
% 2.84/1.36  tff(c_210, plain, (r1_tarski(k2_relat_1('#skF_5'), '#skF_4')), inference(splitRight, [status(thm)], [c_194])).
% 2.84/1.36  tff(c_233, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_209, c_210])).
% 2.84/1.36  tff(c_234, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.36  tff(c_248, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_234])).
% 2.84/1.36  tff(c_28, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.84/1.36  tff(c_260, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_248, c_28])).
% 2.84/1.36  tff(c_14, plain, (![A_10, B_11]: (r2_hidden('#skF_2'(A_10, B_11), k2_relat_1(B_11)) | ~r2_hidden(A_10, k1_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.36  tff(c_217, plain, (![A_10]: (r2_hidden('#skF_2'(A_10, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_10, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_209, c_14])).
% 2.84/1.36  tff(c_301, plain, (![A_90]: (r2_hidden('#skF_2'(A_90, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_90, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_217])).
% 2.84/1.36  tff(c_127, plain, (![A_65, B_4, A_3]: (m1_subset_1(A_65, B_4) | ~r2_hidden(A_65, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_122])).
% 2.84/1.36  tff(c_338, plain, (![A_96, B_97]: (m1_subset_1('#skF_2'(A_96, '#skF_5'), B_97) | ~r1_tarski(k1_xboole_0, B_97) | ~r2_hidden(A_96, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_301, c_127])).
% 2.84/1.36  tff(c_341, plain, (![B_97]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_97) | ~r1_tarski(k1_xboole_0, B_97) | k1_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_338])).
% 2.84/1.36  tff(c_345, plain, (![B_98]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_98) | ~r1_tarski(k1_xboole_0, B_98))), inference(negUnitSimplification, [status(thm)], [c_260, c_341])).
% 2.84/1.36  tff(c_156, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77), k2_relat_1(B_77)) | ~r2_hidden(A_76, k1_relat_1(B_77)) | ~v1_relat_1(B_77))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.84/1.36  tff(c_26, plain, (![D_36]: (~r2_hidden(D_36, k2_relset_1('#skF_3', '#skF_4', '#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.84/1.36  tff(c_145, plain, (![D_36]: (~r2_hidden(D_36, k2_relat_1('#skF_5')) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_143, c_26])).
% 2.84/1.36  tff(c_160, plain, (![A_76]: (~m1_subset_1('#skF_2'(A_76, '#skF_5'), '#skF_4') | ~r2_hidden(A_76, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_156, c_145])).
% 2.84/1.36  tff(c_282, plain, (![A_86]: (~m1_subset_1('#skF_2'(A_86, '#skF_5'), '#skF_4') | ~r2_hidden(A_86, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_160])).
% 2.84/1.36  tff(c_286, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_282])).
% 2.84/1.36  tff(c_289, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_260, c_286])).
% 2.84/1.36  tff(c_348, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_345, c_289])).
% 2.84/1.36  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_233, c_348])).
% 2.84/1.36  tff(c_380, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(splitRight, [status(thm)], [c_61])).
% 2.84/1.36  tff(c_513, plain, (![A_134, B_135, C_136]: (k2_relset_1(A_134, B_135, C_136)=k2_relat_1(C_136) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.84/1.36  tff(c_524, plain, (k2_relset_1('#skF_3', '#skF_4', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_513])).
% 2.84/1.36  tff(c_528, plain, (k2_relat_1('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_380, c_524])).
% 2.84/1.36  tff(c_538, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8) | ~v5_relat_1('#skF_5', A_8) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_528, c_12])).
% 2.84/1.36  tff(c_569, plain, (![A_138]: (r1_tarski(k1_xboole_0, A_138) | ~v5_relat_1('#skF_5', A_138))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_538])).
% 2.84/1.36  tff(c_577, plain, (r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_88, c_569])).
% 2.84/1.36  tff(c_443, plain, (![A_112, B_113, C_114]: (k1_relset_1(A_112, B_113, C_114)=k1_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.84/1.36  tff(c_457, plain, (k1_relset_1('#skF_3', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_443])).
% 2.84/1.36  tff(c_458, plain, (k1_relat_1('#skF_5')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_457, c_28])).
% 2.84/1.36  tff(c_532, plain, (![A_10]: (r2_hidden('#skF_2'(A_10, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_10, k1_relat_1('#skF_5')) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_528, c_14])).
% 2.84/1.36  tff(c_578, plain, (![A_139]: (r2_hidden('#skF_2'(A_139, '#skF_5'), k1_xboole_0) | ~r2_hidden(A_139, k1_relat_1('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_532])).
% 2.84/1.36  tff(c_406, plain, (![A_103, C_104, B_105]: (m1_subset_1(A_103, C_104) | ~m1_subset_1(B_105, k1_zfmisc_1(C_104)) | ~r2_hidden(A_103, B_105))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.36  tff(c_411, plain, (![A_103, B_4, A_3]: (m1_subset_1(A_103, B_4) | ~r2_hidden(A_103, A_3) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_406])).
% 2.84/1.36  tff(c_610, plain, (![A_144, B_145]: (m1_subset_1('#skF_2'(A_144, '#skF_5'), B_145) | ~r1_tarski(k1_xboole_0, B_145) | ~r2_hidden(A_144, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_578, c_411])).
% 2.84/1.36  tff(c_613, plain, (![B_145]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_145) | ~r1_tarski(k1_xboole_0, B_145) | k1_relat_1('#skF_5')=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_610])).
% 2.84/1.36  tff(c_617, plain, (![B_146]: (m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), B_146) | ~r1_tarski(k1_xboole_0, B_146))), inference(negUnitSimplification, [status(thm)], [c_458, c_613])).
% 2.84/1.36  tff(c_382, plain, (![D_36]: (~r2_hidden(D_36, k1_xboole_0) | ~m1_subset_1(D_36, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_380, c_26])).
% 2.84/1.36  tff(c_602, plain, (![A_143]: (~m1_subset_1('#skF_2'(A_143, '#skF_5'), '#skF_4') | ~r2_hidden(A_143, k1_relat_1('#skF_5')))), inference(resolution, [status(thm)], [c_578, c_382])).
% 2.84/1.36  tff(c_606, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4') | k1_relat_1('#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_602])).
% 2.84/1.36  tff(c_609, plain, (~m1_subset_1('#skF_2'('#skF_1'(k1_relat_1('#skF_5')), '#skF_5'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_458, c_606])).
% 2.84/1.36  tff(c_620, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(resolution, [status(thm)], [c_617, c_609])).
% 2.84/1.36  tff(c_651, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_577, c_620])).
% 2.84/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.36  
% 2.84/1.36  Inference rules
% 2.84/1.36  ----------------------
% 2.84/1.36  #Ref     : 0
% 2.84/1.36  #Sup     : 124
% 2.84/1.36  #Fact    : 0
% 2.84/1.36  #Define  : 0
% 2.84/1.36  #Split   : 2
% 2.84/1.36  #Chain   : 0
% 2.84/1.36  #Close   : 0
% 2.84/1.36  
% 2.84/1.36  Ordering : KBO
% 2.84/1.36  
% 2.84/1.36  Simplification rules
% 2.84/1.36  ----------------------
% 2.84/1.36  #Subsume      : 8
% 2.84/1.36  #Demod        : 40
% 2.84/1.36  #Tautology    : 28
% 2.84/1.36  #SimpNegUnit  : 4
% 2.84/1.36  #BackRed      : 8
% 2.84/1.36  
% 2.84/1.36  #Partial instantiations: 0
% 2.84/1.36  #Strategies tried      : 1
% 2.84/1.36  
% 2.84/1.36  Timing (in seconds)
% 2.84/1.36  ----------------------
% 2.84/1.36  Preprocessing        : 0.31
% 2.84/1.36  Parsing              : 0.17
% 2.84/1.36  CNF conversion       : 0.02
% 2.84/1.36  Main loop            : 0.29
% 2.84/1.36  Inferencing          : 0.13
% 2.84/1.36  Reduction            : 0.08
% 2.84/1.36  Demodulation         : 0.05
% 2.84/1.36  BG Simplification    : 0.02
% 2.84/1.36  Subsumption          : 0.04
% 2.84/1.36  Abstraction          : 0.02
% 2.84/1.36  MUC search           : 0.00
% 2.84/1.36  Cooper               : 0.00
% 2.84/1.36  Total                : 0.64
% 2.84/1.36  Index Insertion      : 0.00
% 2.84/1.36  Index Deletion       : 0.00
% 2.84/1.36  Index Matching       : 0.00
% 2.84/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
