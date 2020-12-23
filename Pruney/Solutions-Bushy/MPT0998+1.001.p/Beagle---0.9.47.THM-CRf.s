%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0998+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n031.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:13 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.51s
% Verified   : 
% Statistics : Number of formulae       :  100 ( 195 expanded)
%              Number of leaves         :   30 (  82 expanded)
%              Depth                    :    7
%              Number of atoms          :  158 ( 548 expanded)
%              Number of equality atoms :   46 ( 107 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k1_relset_1 > k2_zfmisc_1 > k1_funct_1 > k10_relat_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_85,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( B != k1_xboole_0
         => ! [E] :
              ( r2_hidden(E,k8_relset_1(A,B,D,C))
            <=> ( r2_hidden(E,A)
                & r2_hidden(k1_funct_1(D,E),C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_funct_2)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_60,axiom,(
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

tff(f_28,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( r2_hidden(D,k1_relat_1(A))
                & r2_hidden(k1_funct_1(A,D),B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d13_funct_1)).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_284,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k8_relset_1(A_113,B_114,C_115,D_116) = k10_relat_1(C_115,D_116)
      | ~ m1_subset_1(C_115,k1_zfmisc_1(k2_zfmisc_1(A_113,B_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_287,plain,(
    ! [D_116] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_116) = k10_relat_1('#skF_6',D_116) ),
    inference(resolution,[status(thm)],[c_40,c_284])).

tff(c_50,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_63,plain,(
    ~ r2_hidden('#skF_8','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_42,plain,(
    v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    ! [A_31,B_32,C_33] :
      ( k1_relset_1(A_31,B_32,C_33) = k1_relat_1(C_33)
      | ~ m1_subset_1(C_33,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_70,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_66])).

tff(c_113,plain,(
    ! [B_54,A_55,C_56] :
      ( k1_xboole_0 = B_54
      | k1_relset_1(A_55,B_54,C_56) = A_55
      | ~ v1_funct_2(C_56,A_55,B_54)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_116,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_113])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_70,c_116])).

tff(c_120,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_119])).

tff(c_57,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_61,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_57])).

tff(c_44,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_84,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k8_relset_1(A_42,B_43,C_44,D_45) = k10_relat_1(C_44,D_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_87,plain,(
    ! [D_45] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_45) = k10_relat_1('#skF_6',D_45) ),
    inference(resolution,[status(thm)],[c_40,c_84])).

tff(c_56,plain,
    ( r2_hidden('#skF_7','#skF_3')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_62,plain,(
    r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_88,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_87,c_62])).

tff(c_8,plain,(
    ! [D_15,A_4,B_11] :
      ( r2_hidden(D_15,k1_relat_1(A_4))
      | ~ r2_hidden(D_15,k10_relat_1(A_4,B_11))
      | ~ v1_funct_1(A_4)
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_100,plain,
    ( r2_hidden('#skF_8',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_8])).

tff(c_103,plain,(
    r2_hidden('#skF_8',k1_relat_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_100])).

tff(c_121,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_103])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_121])).

tff(c_126,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_144,plain,(
    ! [A_66,B_67,C_68,D_69] :
      ( k8_relset_1(A_66,B_67,C_68,D_69) = k10_relat_1(C_68,D_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_66,B_67))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [D_69] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_69) = k10_relat_1('#skF_6',D_69) ),
    inference(resolution,[status(thm)],[c_40,c_144])).

tff(c_148,plain,(
    r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_62])).

tff(c_164,plain,(
    ! [A_71,D_72,B_73] :
      ( r2_hidden(k1_funct_1(A_71,D_72),B_73)
      | ~ r2_hidden(D_72,k10_relat_1(A_71,B_73))
      | ~ v1_funct_1(A_71)
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_125,plain,
    ( ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_128,plain,(
    ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_125])).

tff(c_171,plain,
    ( ~ r2_hidden('#skF_8',k10_relat_1('#skF_6','#skF_5'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_164,c_128])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_148,c_171])).

tff(c_178,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_193,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k8_relset_1(A_81,B_82,C_83,D_84) = k10_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_196,plain,(
    ! [D_84] : k8_relset_1('#skF_3','#skF_4','#skF_6',D_84) = k10_relat_1('#skF_6',D_84) ),
    inference(resolution,[status(thm)],[c_40,c_193])).

tff(c_46,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_221,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_178,c_196,c_46])).

tff(c_177,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_125])).

tff(c_180,plain,(
    ! [A_75,B_76,C_77] :
      ( k1_relset_1(A_75,B_76,C_77) = k1_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_184,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_180])).

tff(c_224,plain,(
    ! [B_95,A_96,C_97] :
      ( k1_xboole_0 = B_95
      | k1_relset_1(A_96,B_95,C_97) = A_96
      | ~ v1_funct_2(C_97,A_96,B_95)
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_96,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_227,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_224])).

tff(c_230,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_184,c_227])).

tff(c_231,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_230])).

tff(c_48,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | ~ r2_hidden(k1_funct_1('#skF_6','#skF_8'),'#skF_5')
    | ~ r2_hidden('#skF_8','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_186,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_178,c_48])).

tff(c_251,plain,(
    ! [D_101,A_102,B_103] :
      ( r2_hidden(D_101,k10_relat_1(A_102,B_103))
      | ~ r2_hidden(k1_funct_1(A_102,D_101),B_103)
      | ~ r2_hidden(D_101,k1_relat_1(A_102))
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_257,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_186,c_251])).

tff(c_264,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_177,c_231,c_257])).

tff(c_266,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_221,c_264])).

tff(c_268,plain,(
    ~ r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_52,plain,
    ( ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5'))
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_288,plain,(
    ~ r2_hidden('#skF_7',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_52])).

tff(c_289,plain,(
    ~ r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_288])).

tff(c_267,plain,(
    r2_hidden('#skF_7','#skF_3') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_271,plain,(
    ! [A_105,B_106,C_107] :
      ( k1_relset_1(A_105,B_106,C_107) = k1_relat_1(C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_105,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_275,plain,(
    k1_relset_1('#skF_3','#skF_4','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_271])).

tff(c_316,plain,(
    ! [B_128,A_129,C_130] :
      ( k1_xboole_0 = B_128
      | k1_relset_1(A_129,B_128,C_130) = A_129
      | ~ v1_funct_2(C_130,A_129,B_128)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(k2_zfmisc_1(A_129,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_319,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4','#skF_6') = '#skF_3'
    | ~ v1_funct_2('#skF_6','#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_316])).

tff(c_322,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_6') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_275,c_319])).

tff(c_323,plain,(
    k1_relat_1('#skF_6') = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_322])).

tff(c_54,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5')
    | r2_hidden('#skF_8',k8_relset_1('#skF_3','#skF_4','#skF_6','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_280,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_268,c_54])).

tff(c_333,plain,(
    ! [D_131,A_132,B_133] :
      ( r2_hidden(D_131,k10_relat_1(A_132,B_133))
      | ~ r2_hidden(k1_funct_1(A_132,D_131),B_133)
      | ~ r2_hidden(D_131,k1_relat_1(A_132))
      | ~ v1_funct_1(A_132)
      | ~ v1_relat_1(A_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_339,plain,
    ( r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5'))
    | ~ r2_hidden('#skF_7',k1_relat_1('#skF_6'))
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_280,c_333])).

tff(c_343,plain,(
    r2_hidden('#skF_7',k10_relat_1('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_44,c_267,c_323,c_339])).

tff(c_345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_289,c_343])).

%------------------------------------------------------------------------------
