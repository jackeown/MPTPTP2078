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
% DateTime   : Thu Dec  3 10:12:52 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.02s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 553 expanded)
%              Number of leaves         :   33 ( 209 expanded)
%              Depth                    :   14
%              Number of atoms          :  250 (1650 expanded)
%              Number of equality atoms :   43 ( 253 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k10_relat_1(B,A) = k9_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t155_funct_1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k8_relset_1(A,B,C,D),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_93,plain,(
    ! [B_38,A_39] :
      ( v1_relat_1(B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_39))
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_99,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_93])).

tff(c_103,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_99])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_38,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_18,plain,(
    ! [A_12] :
      ( k2_relat_1(k2_funct_1(A_12)) = k1_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_14,plain,(
    ! [A_9] :
      ( v1_relat_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_146,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_153,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_146])).

tff(c_156,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_153])).

tff(c_125,plain,(
    ! [A_43] :
      ( k1_relat_1(k2_funct_1(A_43)) = k2_relat_1(A_43)
      | ~ v2_funct_1(A_43)
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_8] :
      ( k9_relat_1(A_8,k1_relat_1(A_8)) = k2_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_369,plain,(
    ! [A_93] :
      ( k9_relat_1(k2_funct_1(A_93),k2_relat_1(A_93)) = k2_relat_1(k2_funct_1(A_93))
      | ~ v1_relat_1(k2_funct_1(A_93))
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_10])).

tff(c_385,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_369])).

tff(c_392,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_385])).

tff(c_393,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_392])).

tff(c_396,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_393])).

tff(c_400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_396])).

tff(c_401,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k9_relat_1(k2_funct_1(B_11),A_10) = k10_relat_1(B_11,A_10)
      | ~ v2_funct_1(B_11)
      | ~ v1_funct_1(B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_406,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_401,c_16])).

tff(c_413,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_406])).

tff(c_426,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_18])).

tff(c_437,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_426])).

tff(c_188,plain,(
    ! [A_55,B_56,C_57,D_58] :
      ( k8_relset_1(A_55,B_56,C_57,D_58) = k10_relat_1(C_57,D_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_195,plain,(
    ! [D_58] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_58) = k10_relat_1('#skF_3',D_58) ),
    inference(resolution,[status(thm)],[c_40,c_188])).

tff(c_210,plain,(
    ! [A_64,B_65,C_66,D_67] :
      ( m1_subset_1(k8_relset_1(A_64,B_65,C_66,D_67),k1_zfmisc_1(A_64))
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_64,B_65))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_226,plain,(
    ! [D_58] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_58),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_210])).

tff(c_233,plain,(
    ! [D_68] : m1_subset_1(k10_relat_1('#skF_3',D_68),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_226])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_241,plain,(
    ! [D_68] : r1_tarski(k10_relat_1('#skF_3',D_68),'#skF_1') ),
    inference(resolution,[status(thm)],[c_233,c_2])).

tff(c_468,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_241])).

tff(c_402,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_392])).

tff(c_12,plain,(
    ! [A_9] :
      ( v1_funct_1(k2_funct_1(A_9))
      | ~ v1_funct_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_34,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_53,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_56,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_53])).

tff(c_59,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_56])).

tff(c_69,plain,(
    ! [B_34,A_35] :
      ( v1_relat_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_35))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_69])).

tff(c_79,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_75])).

tff(c_81,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_79])).

tff(c_83,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_465,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_413])).

tff(c_20,plain,(
    ! [A_12] :
      ( k1_relat_1(k2_funct_1(A_12)) = k2_relat_1(A_12)
      | ~ v2_funct_1(A_12)
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_302,plain,(
    ! [B_86,A_87] :
      ( m1_subset_1(B_86,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_86),A_87)))
      | ~ r1_tarski(k2_relat_1(B_86),A_87)
      | ~ v1_funct_1(B_86)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_763,plain,(
    ! [A_122,A_123] :
      ( m1_subset_1(k2_funct_1(A_122),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122),A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_122)),A_123)
      | ~ v1_funct_1(k2_funct_1(A_122))
      | ~ v1_relat_1(k2_funct_1(A_122))
      | ~ v2_funct_1(A_122)
      | ~ v1_funct_1(A_122)
      | ~ v1_relat_1(A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_302])).

tff(c_784,plain,(
    ! [A_123] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_123)))
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_123)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_763])).

tff(c_800,plain,(
    ! [A_124] :
      ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2',A_124)))
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_124) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_402,c_83,c_465,c_784])).

tff(c_82,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_104,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_812,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_800,c_104])).

tff(c_827,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_812])).

tff(c_829,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_6,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_832,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_829,c_6])).

tff(c_838,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_832])).

tff(c_906,plain,(
    ! [B_133,A_134] :
      ( k9_relat_1(k2_funct_1(B_133),A_134) = k10_relat_1(B_133,A_134)
      | ~ v2_funct_1(B_133)
      | ~ v1_funct_1(B_133)
      | ~ v1_relat_1(B_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1214,plain,(
    ! [B_188] :
      ( k10_relat_1(B_188,k1_relat_1(k2_funct_1(B_188))) = k2_relat_1(k2_funct_1(B_188))
      | ~ v2_funct_1(B_188)
      | ~ v1_funct_1(B_188)
      | ~ v1_relat_1(B_188)
      | ~ v1_relat_1(k2_funct_1(B_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_906])).

tff(c_938,plain,(
    ! [A_140,B_141,C_142,D_143] :
      ( k8_relset_1(A_140,B_141,C_142,D_143) = k10_relat_1(C_142,D_143)
      | ~ m1_subset_1(C_142,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_948,plain,(
    ! [D_143] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_143) = k10_relat_1('#skF_3',D_143) ),
    inference(resolution,[status(thm)],[c_40,c_938])).

tff(c_967,plain,(
    ! [A_146,B_147,C_148,D_149] :
      ( m1_subset_1(k8_relset_1(A_146,B_147,C_148,D_149),k1_zfmisc_1(A_146))
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_986,plain,(
    ! [D_143] :
      ( m1_subset_1(k10_relat_1('#skF_3',D_143),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_948,c_967])).

tff(c_995,plain,(
    ! [D_150] : m1_subset_1(k10_relat_1('#skF_3',D_150),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_986])).

tff(c_1003,plain,(
    ! [D_150] : r1_tarski(k10_relat_1('#skF_3',D_150),'#skF_1') ),
    inference(resolution,[status(thm)],[c_995,c_2])).

tff(c_1229,plain,
    ( r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1214,c_1003])).

tff(c_1246,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_838,c_103,c_44,c_38,c_1229])).

tff(c_1259,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1246])).

tff(c_1268,plain,(
    r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_1259])).

tff(c_883,plain,(
    ! [A_130,B_131,C_132] :
      ( k2_relset_1(A_130,B_131,C_132) = k2_relat_1(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_893,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_883])).

tff(c_897,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_893])).

tff(c_862,plain,(
    ! [A_128] :
      ( k1_relat_1(k2_funct_1(A_128)) = k2_relat_1(A_128)
      | ~ v2_funct_1(A_128)
      | ~ v1_funct_1(A_128)
      | ~ v1_relat_1(A_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1316,plain,(
    ! [A_189] :
      ( k9_relat_1(k2_funct_1(A_189),k2_relat_1(A_189)) = k2_relat_1(k2_funct_1(A_189))
      | ~ v1_relat_1(k2_funct_1(A_189))
      | ~ v2_funct_1(A_189)
      | ~ v1_funct_1(A_189)
      | ~ v1_relat_1(A_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_10])).

tff(c_1332,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_1316])).

tff(c_1339,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_838,c_1332])).

tff(c_1343,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1339,c_16])).

tff(c_1350,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k10_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_1343])).

tff(c_1371,plain,
    ( k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_18])).

tff(c_1384,plain,(
    k10_relat_1('#skF_3','#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_1371])).

tff(c_1388,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1384,c_1350])).

tff(c_934,plain,(
    ! [B_138,A_139] :
      ( v1_funct_2(B_138,k1_relat_1(B_138),A_139)
      | ~ r1_tarski(k2_relat_1(B_138),A_139)
      | ~ v1_funct_1(B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1460,plain,(
    ! [A_190,A_191] :
      ( v1_funct_2(k2_funct_1(A_190),k2_relat_1(A_190),A_191)
      | ~ r1_tarski(k2_relat_1(k2_funct_1(A_190)),A_191)
      | ~ v1_funct_1(k2_funct_1(A_190))
      | ~ v1_relat_1(k2_funct_1(A_190))
      | ~ v2_funct_1(A_190)
      | ~ v1_funct_1(A_190)
      | ~ v1_relat_1(A_190) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_934])).

tff(c_1466,plain,(
    ! [A_191] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_191)
      | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),A_191)
      | ~ v1_funct_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_1460])).

tff(c_1474,plain,(
    ! [A_192] :
      ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2',A_192)
      | ~ r1_tarski(k1_relat_1('#skF_3'),A_192) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_44,c_38,c_838,c_83,c_1388,c_1466])).

tff(c_828,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_1477,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1474,c_828])).

tff(c_1481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1268,c_1477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:57:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.70  
% 4.02/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.70  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k2_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.02/1.70  
% 4.02/1.70  %Foreground sorts:
% 4.02/1.70  
% 4.02/1.70  
% 4.02/1.70  %Background operators:
% 4.02/1.70  
% 4.02/1.70  
% 4.02/1.70  %Foreground operators:
% 4.02/1.70  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.02/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.02/1.70  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.02/1.70  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.02/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.02/1.70  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.02/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.02/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.02/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.02/1.70  tff('#skF_2', type, '#skF_2': $i).
% 4.02/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.02/1.70  tff('#skF_3', type, '#skF_3': $i).
% 4.02/1.70  tff('#skF_1', type, '#skF_1': $i).
% 4.02/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.02/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.02/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.02/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.02/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.02/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.02/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.02/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.02/1.70  
% 4.02/1.73  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.02/1.73  tff(f_109, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 4.02/1.73  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.02/1.73  tff(f_68, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 4.02/1.73  tff(f_50, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 4.02/1.73  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.02/1.73  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.02/1.73  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k10_relat_1(B, A) = k9_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t155_funct_1)).
% 4.02/1.73  tff(f_80, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.02/1.73  tff(f_72, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k8_relset_1(A, B, C, D), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_relset_1)).
% 4.02/1.73  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.02/1.73  tff(f_92, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_funct_2)).
% 4.02/1.73  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.02/1.73  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.73  tff(c_93, plain, (![B_38, A_39]: (v1_relat_1(B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_39)) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_99, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_93])).
% 4.02/1.73  tff(c_103, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_99])).
% 4.02/1.73  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.73  tff(c_38, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.73  tff(c_18, plain, (![A_12]: (k2_relat_1(k2_funct_1(A_12))=k1_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.02/1.73  tff(c_14, plain, (![A_9]: (v1_relat_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.02/1.73  tff(c_36, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.73  tff(c_146, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.02/1.73  tff(c_153, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_146])).
% 4.02/1.73  tff(c_156, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_153])).
% 4.02/1.73  tff(c_125, plain, (![A_43]: (k1_relat_1(k2_funct_1(A_43))=k2_relat_1(A_43) | ~v2_funct_1(A_43) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.02/1.73  tff(c_10, plain, (![A_8]: (k9_relat_1(A_8, k1_relat_1(A_8))=k2_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.02/1.73  tff(c_369, plain, (![A_93]: (k9_relat_1(k2_funct_1(A_93), k2_relat_1(A_93))=k2_relat_1(k2_funct_1(A_93)) | ~v1_relat_1(k2_funct_1(A_93)) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(superposition, [status(thm), theory('equality')], [c_125, c_10])).
% 4.02/1.73  tff(c_385, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_156, c_369])).
% 4.02/1.73  tff(c_392, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_385])).
% 4.02/1.73  tff(c_393, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_392])).
% 4.02/1.73  tff(c_396, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_393])).
% 4.02/1.73  tff(c_400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_396])).
% 4.02/1.73  tff(c_401, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_392])).
% 4.02/1.73  tff(c_16, plain, (![B_11, A_10]: (k9_relat_1(k2_funct_1(B_11), A_10)=k10_relat_1(B_11, A_10) | ~v2_funct_1(B_11) | ~v1_funct_1(B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.02/1.73  tff(c_406, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_401, c_16])).
% 4.02/1.73  tff(c_413, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_406])).
% 4.02/1.73  tff(c_426, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_413, c_18])).
% 4.02/1.73  tff(c_437, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_426])).
% 4.02/1.73  tff(c_188, plain, (![A_55, B_56, C_57, D_58]: (k8_relset_1(A_55, B_56, C_57, D_58)=k10_relat_1(C_57, D_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.02/1.73  tff(c_195, plain, (![D_58]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_58)=k10_relat_1('#skF_3', D_58))), inference(resolution, [status(thm)], [c_40, c_188])).
% 4.02/1.73  tff(c_210, plain, (![A_64, B_65, C_66, D_67]: (m1_subset_1(k8_relset_1(A_64, B_65, C_66, D_67), k1_zfmisc_1(A_64)) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_64, B_65))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.02/1.73  tff(c_226, plain, (![D_58]: (m1_subset_1(k10_relat_1('#skF_3', D_58), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_195, c_210])).
% 4.02/1.73  tff(c_233, plain, (![D_68]: (m1_subset_1(k10_relat_1('#skF_3', D_68), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_226])).
% 4.02/1.73  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.02/1.73  tff(c_241, plain, (![D_68]: (r1_tarski(k10_relat_1('#skF_3', D_68), '#skF_1'))), inference(resolution, [status(thm)], [c_233, c_2])).
% 4.02/1.73  tff(c_468, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_437, c_241])).
% 4.02/1.73  tff(c_402, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_392])).
% 4.02/1.73  tff(c_12, plain, (![A_9]: (v1_funct_1(k2_funct_1(A_9)) | ~v1_funct_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.02/1.73  tff(c_34, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.02/1.73  tff(c_53, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 4.02/1.73  tff(c_56, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_53])).
% 4.02/1.73  tff(c_59, plain, (~v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_56])).
% 4.02/1.73  tff(c_69, plain, (![B_34, A_35]: (v1_relat_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_35)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_75, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_69])).
% 4.02/1.73  tff(c_79, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_75])).
% 4.02/1.73  tff(c_81, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_79])).
% 4.02/1.73  tff(c_83, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 4.02/1.73  tff(c_465, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_413])).
% 4.02/1.73  tff(c_20, plain, (![A_12]: (k1_relat_1(k2_funct_1(A_12))=k2_relat_1(A_12) | ~v2_funct_1(A_12) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.02/1.73  tff(c_302, plain, (![B_86, A_87]: (m1_subset_1(B_86, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_86), A_87))) | ~r1_tarski(k2_relat_1(B_86), A_87) | ~v1_funct_1(B_86) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.02/1.73  tff(c_763, plain, (![A_122, A_123]: (m1_subset_1(k2_funct_1(A_122), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_122), A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1(A_122)), A_123) | ~v1_funct_1(k2_funct_1(A_122)) | ~v1_relat_1(k2_funct_1(A_122)) | ~v2_funct_1(A_122) | ~v1_funct_1(A_122) | ~v1_relat_1(A_122))), inference(superposition, [status(thm), theory('equality')], [c_20, c_302])).
% 4.02/1.73  tff(c_784, plain, (![A_123]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_123))) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_123) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_156, c_763])).
% 4.02/1.73  tff(c_800, plain, (![A_124]: (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', A_124))) | ~r1_tarski(k1_relat_1('#skF_3'), A_124))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_402, c_83, c_465, c_784])).
% 4.02/1.73  tff(c_82, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_34])).
% 4.02/1.73  tff(c_104, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_82])).
% 4.02/1.73  tff(c_812, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_800, c_104])).
% 4.02/1.73  tff(c_827, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_468, c_812])).
% 4.02/1.73  tff(c_829, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_82])).
% 4.02/1.73  tff(c_6, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.02/1.73  tff(c_832, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_829, c_6])).
% 4.02/1.73  tff(c_838, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_832])).
% 4.02/1.73  tff(c_906, plain, (![B_133, A_134]: (k9_relat_1(k2_funct_1(B_133), A_134)=k10_relat_1(B_133, A_134) | ~v2_funct_1(B_133) | ~v1_funct_1(B_133) | ~v1_relat_1(B_133))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.02/1.73  tff(c_1214, plain, (![B_188]: (k10_relat_1(B_188, k1_relat_1(k2_funct_1(B_188)))=k2_relat_1(k2_funct_1(B_188)) | ~v2_funct_1(B_188) | ~v1_funct_1(B_188) | ~v1_relat_1(B_188) | ~v1_relat_1(k2_funct_1(B_188)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_906])).
% 4.02/1.73  tff(c_938, plain, (![A_140, B_141, C_142, D_143]: (k8_relset_1(A_140, B_141, C_142, D_143)=k10_relat_1(C_142, D_143) | ~m1_subset_1(C_142, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.02/1.73  tff(c_948, plain, (![D_143]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_143)=k10_relat_1('#skF_3', D_143))), inference(resolution, [status(thm)], [c_40, c_938])).
% 4.02/1.73  tff(c_967, plain, (![A_146, B_147, C_148, D_149]: (m1_subset_1(k8_relset_1(A_146, B_147, C_148, D_149), k1_zfmisc_1(A_146)) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.02/1.73  tff(c_986, plain, (![D_143]: (m1_subset_1(k10_relat_1('#skF_3', D_143), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_948, c_967])).
% 4.02/1.73  tff(c_995, plain, (![D_150]: (m1_subset_1(k10_relat_1('#skF_3', D_150), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_986])).
% 4.02/1.73  tff(c_1003, plain, (![D_150]: (r1_tarski(k10_relat_1('#skF_3', D_150), '#skF_1'))), inference(resolution, [status(thm)], [c_995, c_2])).
% 4.02/1.73  tff(c_1229, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1214, c_1003])).
% 4.02/1.73  tff(c_1246, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_838, c_103, c_44, c_38, c_1229])).
% 4.02/1.73  tff(c_1259, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_18, c_1246])).
% 4.02/1.73  tff(c_1268, plain, (r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_1259])).
% 4.02/1.73  tff(c_883, plain, (![A_130, B_131, C_132]: (k2_relset_1(A_130, B_131, C_132)=k2_relat_1(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.02/1.73  tff(c_893, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_883])).
% 4.02/1.73  tff(c_897, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_893])).
% 4.02/1.73  tff(c_862, plain, (![A_128]: (k1_relat_1(k2_funct_1(A_128))=k2_relat_1(A_128) | ~v2_funct_1(A_128) | ~v1_funct_1(A_128) | ~v1_relat_1(A_128))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.02/1.73  tff(c_1316, plain, (![A_189]: (k9_relat_1(k2_funct_1(A_189), k2_relat_1(A_189))=k2_relat_1(k2_funct_1(A_189)) | ~v1_relat_1(k2_funct_1(A_189)) | ~v2_funct_1(A_189) | ~v1_funct_1(A_189) | ~v1_relat_1(A_189))), inference(superposition, [status(thm), theory('equality')], [c_862, c_10])).
% 4.02/1.73  tff(c_1332, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_897, c_1316])).
% 4.02/1.73  tff(c_1339, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_838, c_1332])).
% 4.02/1.73  tff(c_1343, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1339, c_16])).
% 4.02/1.73  tff(c_1350, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k10_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_1343])).
% 4.02/1.73  tff(c_1371, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_18])).
% 4.02/1.73  tff(c_1384, plain, (k10_relat_1('#skF_3', '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_1371])).
% 4.02/1.73  tff(c_1388, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1384, c_1350])).
% 4.02/1.73  tff(c_934, plain, (![B_138, A_139]: (v1_funct_2(B_138, k1_relat_1(B_138), A_139) | ~r1_tarski(k2_relat_1(B_138), A_139) | ~v1_funct_1(B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.02/1.73  tff(c_1460, plain, (![A_190, A_191]: (v1_funct_2(k2_funct_1(A_190), k2_relat_1(A_190), A_191) | ~r1_tarski(k2_relat_1(k2_funct_1(A_190)), A_191) | ~v1_funct_1(k2_funct_1(A_190)) | ~v1_relat_1(k2_funct_1(A_190)) | ~v2_funct_1(A_190) | ~v1_funct_1(A_190) | ~v1_relat_1(A_190))), inference(superposition, [status(thm), theory('equality')], [c_20, c_934])).
% 4.02/1.73  tff(c_1466, plain, (![A_191]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_191) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), A_191) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_897, c_1460])).
% 4.02/1.73  tff(c_1474, plain, (![A_192]: (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', A_192) | ~r1_tarski(k1_relat_1('#skF_3'), A_192))), inference(demodulation, [status(thm), theory('equality')], [c_103, c_44, c_38, c_838, c_83, c_1388, c_1466])).
% 4.02/1.73  tff(c_828, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_82])).
% 4.02/1.73  tff(c_1477, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1474, c_828])).
% 4.02/1.73  tff(c_1481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1268, c_1477])).
% 4.02/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.02/1.73  
% 4.02/1.73  Inference rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Ref     : 0
% 4.02/1.73  #Sup     : 329
% 4.02/1.73  #Fact    : 0
% 4.02/1.73  #Define  : 0
% 4.02/1.73  #Split   : 15
% 4.02/1.73  #Chain   : 0
% 4.02/1.73  #Close   : 0
% 4.02/1.73  
% 4.02/1.73  Ordering : KBO
% 4.02/1.73  
% 4.02/1.73  Simplification rules
% 4.02/1.73  ----------------------
% 4.02/1.73  #Subsume      : 56
% 4.02/1.73  #Demod        : 288
% 4.02/1.73  #Tautology    : 125
% 4.02/1.73  #SimpNegUnit  : 2
% 4.02/1.73  #BackRed      : 9
% 4.02/1.73  
% 4.02/1.73  #Partial instantiations: 0
% 4.02/1.73  #Strategies tried      : 1
% 4.02/1.73  
% 4.02/1.73  Timing (in seconds)
% 4.02/1.73  ----------------------
% 4.02/1.73  Preprocessing        : 0.33
% 4.02/1.73  Parsing              : 0.17
% 4.02/1.73  CNF conversion       : 0.02
% 4.02/1.73  Main loop            : 0.62
% 4.02/1.73  Inferencing          : 0.24
% 4.02/1.73  Reduction            : 0.20
% 4.02/1.73  Demodulation         : 0.14
% 4.02/1.73  BG Simplification    : 0.03
% 4.02/1.73  Subsumption          : 0.10
% 4.02/1.73  Abstraction          : 0.03
% 4.02/1.73  MUC search           : 0.00
% 4.02/1.73  Cooper               : 0.00
% 4.02/1.73  Total                : 1.00
% 4.02/1.73  Index Insertion      : 0.00
% 4.02/1.73  Index Deletion       : 0.00
% 4.02/1.73  Index Matching       : 0.00
% 4.02/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
