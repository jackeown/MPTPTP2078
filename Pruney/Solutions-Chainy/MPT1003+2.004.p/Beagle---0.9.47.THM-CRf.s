%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:58 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 266 expanded)
%              Number of leaves         :   34 (  98 expanded)
%              Depth                    :   13
%              Number of atoms          :  135 ( 602 expanded)
%              Number of equality atoms :   66 ( 306 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => k8_relset_1(A,B,C,k7_relset_1(A,B,C,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_38,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_45,plain,(
    ! [B_30,A_31] :
      ( v1_relat_1(B_30)
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_31))
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_48,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_45])).

tff(c_51,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_129,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k8_relset_1(A_54,B_55,C_56,D_57) = k10_relat_1(C_56,D_57)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_132,plain,(
    ! [D_57] : k8_relset_1('#skF_1','#skF_2','#skF_3',D_57) = k10_relat_1('#skF_3',D_57) ),
    inference(resolution,[status(thm)],[c_38,c_129])).

tff(c_79,plain,(
    ! [C_40,A_41,B_42] :
      ( v4_relat_1(C_40,A_41)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_83,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_91,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_83,c_10])).

tff(c_94,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_91])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_98,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_6])).

tff(c_102,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_98])).

tff(c_113,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k7_relset_1(A_47,B_48,C_49,D_50) = k9_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_116,plain,(
    ! [D_50] : k7_relset_1('#skF_1','#skF_2','#skF_3',D_50) = k9_relat_1('#skF_3',D_50) ),
    inference(resolution,[status(thm)],[c_38,c_113])).

tff(c_34,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k7_relset_1('#skF_1','#skF_2','#skF_3','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_117,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_34])).

tff(c_118,plain,(
    k8_relset_1('#skF_1','#skF_2','#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_117])).

tff(c_133,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_118])).

tff(c_145,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_133])).

tff(c_147,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_145])).

tff(c_36,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_43,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_40,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_84,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_84])).

tff(c_150,plain,(
    ! [B_63,A_64,C_65] :
      ( k1_xboole_0 = B_63
      | k1_relset_1(A_64,B_63,C_65) = A_64
      | ~ v1_funct_2(C_65,A_64,B_63)
      | ~ m1_subset_1(C_65,k1_zfmisc_1(k2_zfmisc_1(A_64,B_63))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_153,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_150])).

tff(c_156,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_88,c_153])).

tff(c_158,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_43,c_156])).

tff(c_159,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_160,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_165,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_160])).

tff(c_172,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_38])).

tff(c_173,plain,(
    ! [B_68,A_69] :
      ( v1_relat_1(B_68)
      | ~ m1_subset_1(B_68,k1_zfmisc_1(A_69))
      | ~ v1_relat_1(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_176,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_172,c_173])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_176])).

tff(c_203,plain,(
    ! [C_75,A_76,B_77] :
      ( v4_relat_1(C_75,A_76)
      | ~ m1_subset_1(C_75,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_207,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_172,c_203])).

tff(c_210,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_207,c_10])).

tff(c_213,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_210])).

tff(c_222,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_213,c_6])).

tff(c_226,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_222])).

tff(c_266,plain,(
    ! [A_92,B_93,C_94,D_95] :
      ( k7_relset_1(A_92,B_93,C_94,D_95) = k9_relat_1(C_94,D_95)
      | ~ m1_subset_1(C_94,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_269,plain,(
    ! [D_95] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_95) = k9_relat_1('#skF_3',D_95) ),
    inference(resolution,[status(thm)],[c_172,c_266])).

tff(c_243,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k8_relset_1(A_85,B_86,C_87,D_88) = k10_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_246,plain,(
    ! [D_88] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_88) = k10_relat_1('#skF_3',D_88) ),
    inference(resolution,[status(thm)],[c_172,c_243])).

tff(c_180,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_165,c_34])).

tff(c_247,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_180])).

tff(c_270,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_247])).

tff(c_271,plain,(
    k10_relat_1('#skF_3',k2_relat_1('#skF_3')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_270])).

tff(c_283,plain,
    ( k1_relat_1('#skF_3') != '#skF_1'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_271])).

tff(c_285,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_283])).

tff(c_166,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_40])).

tff(c_234,plain,(
    ! [A_82,B_83,C_84] :
      ( k1_relset_1(A_82,B_83,C_84) = k1_relat_1(C_84)
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_82,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_238,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_234])).

tff(c_30,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_287,plain,(
    ! [B_97,C_98] :
      ( k1_relset_1('#skF_1',B_97,C_98) = '#skF_1'
      | ~ v1_funct_2(C_98,'#skF_1',B_97)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_97))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_159,c_159,c_159,c_30])).

tff(c_290,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_172,c_287])).

tff(c_293,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_238,c_290])).

tff(c_295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:04:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.28  
% 2.33/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.29  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.33/1.29  
% 2.33/1.29  %Foreground sorts:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Background operators:
% 2.33/1.29  
% 2.33/1.29  
% 2.33/1.29  %Foreground operators:
% 2.33/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.33/1.29  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.33/1.29  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.33/1.29  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.33/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.29  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.33/1.29  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.33/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.33/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.29  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.33/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.29  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.33/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.33/1.29  
% 2.33/1.30  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.33/1.30  tff(f_97, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, k7_relset_1(A, B, C, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_funct_2)).
% 2.33/1.30  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.33/1.30  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.33/1.30  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.33/1.30  tff(f_54, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.33/1.30  tff(f_48, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 2.33/1.30  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.33/1.30  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.33/1.30  tff(f_58, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.33/1.30  tff(f_84, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.33/1.30  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.33/1.30  tff(c_38, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.33/1.30  tff(c_45, plain, (![B_30, A_31]: (v1_relat_1(B_30) | ~m1_subset_1(B_30, k1_zfmisc_1(A_31)) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.30  tff(c_48, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_45])).
% 2.33/1.30  tff(c_51, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_48])).
% 2.33/1.30  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.33/1.30  tff(c_129, plain, (![A_54, B_55, C_56, D_57]: (k8_relset_1(A_54, B_55, C_56, D_57)=k10_relat_1(C_56, D_57) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.30  tff(c_132, plain, (![D_57]: (k8_relset_1('#skF_1', '#skF_2', '#skF_3', D_57)=k10_relat_1('#skF_3', D_57))), inference(resolution, [status(thm)], [c_38, c_129])).
% 2.33/1.30  tff(c_79, plain, (![C_40, A_41, B_42]: (v4_relat_1(C_40, A_41) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.30  tff(c_83, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.33/1.30  tff(c_10, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.33/1.30  tff(c_91, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_83, c_10])).
% 2.33/1.30  tff(c_94, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_91])).
% 2.33/1.30  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.33/1.30  tff(c_98, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_94, c_6])).
% 2.33/1.30  tff(c_102, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_51, c_98])).
% 2.33/1.30  tff(c_113, plain, (![A_47, B_48, C_49, D_50]: (k7_relset_1(A_47, B_48, C_49, D_50)=k9_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.30  tff(c_116, plain, (![D_50]: (k7_relset_1('#skF_1', '#skF_2', '#skF_3', D_50)=k9_relat_1('#skF_3', D_50))), inference(resolution, [status(thm)], [c_38, c_113])).
% 2.33/1.30  tff(c_34, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k7_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.33/1.30  tff(c_117, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_34])).
% 2.33/1.30  tff(c_118, plain, (k8_relset_1('#skF_1', '#skF_2', '#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_117])).
% 2.33/1.30  tff(c_133, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_118])).
% 2.33/1.30  tff(c_145, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_133])).
% 2.33/1.30  tff(c_147, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_51, c_145])).
% 2.33/1.30  tff(c_36, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.33/1.30  tff(c_43, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_36])).
% 2.33/1.30  tff(c_40, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.33/1.30  tff(c_84, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.30  tff(c_88, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_84])).
% 2.33/1.30  tff(c_150, plain, (![B_63, A_64, C_65]: (k1_xboole_0=B_63 | k1_relset_1(A_64, B_63, C_65)=A_64 | ~v1_funct_2(C_65, A_64, B_63) | ~m1_subset_1(C_65, k1_zfmisc_1(k2_zfmisc_1(A_64, B_63))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.33/1.30  tff(c_153, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_150])).
% 2.33/1.30  tff(c_156, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_88, c_153])).
% 2.33/1.30  tff(c_158, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_43, c_156])).
% 2.33/1.30  tff(c_159, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.33/1.30  tff(c_160, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 2.33/1.30  tff(c_165, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_160])).
% 2.33/1.30  tff(c_172, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_165, c_38])).
% 2.33/1.30  tff(c_173, plain, (![B_68, A_69]: (v1_relat_1(B_68) | ~m1_subset_1(B_68, k1_zfmisc_1(A_69)) | ~v1_relat_1(A_69))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.30  tff(c_176, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_172, c_173])).
% 2.33/1.30  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_176])).
% 2.33/1.30  tff(c_203, plain, (![C_75, A_76, B_77]: (v4_relat_1(C_75, A_76) | ~m1_subset_1(C_75, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.30  tff(c_207, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_172, c_203])).
% 2.33/1.30  tff(c_210, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_207, c_10])).
% 2.33/1.30  tff(c_213, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_210])).
% 2.33/1.30  tff(c_222, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_213, c_6])).
% 2.33/1.30  tff(c_226, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_222])).
% 2.33/1.30  tff(c_266, plain, (![A_92, B_93, C_94, D_95]: (k7_relset_1(A_92, B_93, C_94, D_95)=k9_relat_1(C_94, D_95) | ~m1_subset_1(C_94, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.33/1.30  tff(c_269, plain, (![D_95]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_95)=k9_relat_1('#skF_3', D_95))), inference(resolution, [status(thm)], [c_172, c_266])).
% 2.33/1.30  tff(c_243, plain, (![A_85, B_86, C_87, D_88]: (k8_relset_1(A_85, B_86, C_87, D_88)=k10_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.33/1.30  tff(c_246, plain, (![D_88]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_88)=k10_relat_1('#skF_3', D_88))), inference(resolution, [status(thm)], [c_172, c_243])).
% 2.33/1.30  tff(c_180, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_165, c_34])).
% 2.33/1.30  tff(c_247, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_180])).
% 2.33/1.30  tff(c_270, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_269, c_247])).
% 2.33/1.30  tff(c_271, plain, (k10_relat_1('#skF_3', k2_relat_1('#skF_3'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_270])).
% 2.33/1.30  tff(c_283, plain, (k1_relat_1('#skF_3')!='#skF_1' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8, c_271])).
% 2.33/1.30  tff(c_285, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_283])).
% 2.33/1.30  tff(c_166, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_165, c_40])).
% 2.33/1.30  tff(c_234, plain, (![A_82, B_83, C_84]: (k1_relset_1(A_82, B_83, C_84)=k1_relat_1(C_84) | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_82, B_83))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.33/1.30  tff(c_238, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_172, c_234])).
% 2.33/1.30  tff(c_30, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.33/1.30  tff(c_287, plain, (![B_97, C_98]: (k1_relset_1('#skF_1', B_97, C_98)='#skF_1' | ~v1_funct_2(C_98, '#skF_1', B_97) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_97))))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_159, c_159, c_159, c_30])).
% 2.33/1.30  tff(c_290, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_172, c_287])).
% 2.33/1.30  tff(c_293, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_238, c_290])).
% 2.33/1.30  tff(c_295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_293])).
% 2.33/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.30  
% 2.33/1.30  Inference rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Ref     : 0
% 2.33/1.30  #Sup     : 55
% 2.33/1.30  #Fact    : 0
% 2.33/1.30  #Define  : 0
% 2.33/1.30  #Split   : 1
% 2.33/1.30  #Chain   : 0
% 2.33/1.30  #Close   : 0
% 2.33/1.30  
% 2.33/1.30  Ordering : KBO
% 2.33/1.30  
% 2.33/1.30  Simplification rules
% 2.33/1.30  ----------------------
% 2.33/1.30  #Subsume      : 0
% 2.33/1.30  #Demod        : 37
% 2.33/1.30  #Tautology    : 33
% 2.33/1.30  #SimpNegUnit  : 2
% 2.33/1.30  #BackRed      : 5
% 2.33/1.30  
% 2.33/1.30  #Partial instantiations: 0
% 2.33/1.30  #Strategies tried      : 1
% 2.33/1.30  
% 2.33/1.30  Timing (in seconds)
% 2.33/1.30  ----------------------
% 2.33/1.31  Preprocessing        : 0.32
% 2.33/1.31  Parsing              : 0.17
% 2.33/1.31  CNF conversion       : 0.02
% 2.33/1.31  Main loop            : 0.21
% 2.33/1.31  Inferencing          : 0.08
% 2.33/1.31  Reduction            : 0.06
% 2.33/1.31  Demodulation         : 0.05
% 2.33/1.31  BG Simplification    : 0.02
% 2.33/1.31  Subsumption          : 0.02
% 2.33/1.31  Abstraction          : 0.01
% 2.33/1.31  MUC search           : 0.00
% 2.33/1.31  Cooper               : 0.00
% 2.33/1.31  Total                : 0.56
% 2.33/1.31  Index Insertion      : 0.00
% 2.33/1.31  Index Deletion       : 0.00
% 2.33/1.31  Index Matching       : 0.00
% 2.33/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
