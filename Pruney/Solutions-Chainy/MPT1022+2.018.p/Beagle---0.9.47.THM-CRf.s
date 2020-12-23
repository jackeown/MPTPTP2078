%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.42s
% Verified   : 
% Statistics : Number of formulae       :  154 ( 604 expanded)
%              Number of leaves         :   39 ( 224 expanded)
%              Depth                    :   13
%              Number of atoms          :  279 (1637 expanded)
%              Number of equality atoms :   83 ( 422 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_110,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k8_relset_1(A,B,C,B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_funct_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_12,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_367,plain,(
    ! [B_91,A_92] :
      ( v1_relat_1(B_91)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92))
      | ~ v1_relat_1(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_370,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_367])).

tff(c_373,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_370])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_48,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_1096,plain,(
    ! [C_191,A_192,B_193] :
      ( v2_funct_1(C_191)
      | ~ v3_funct_2(C_191,A_192,B_193)
      | ~ v1_funct_1(C_191)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_192,B_193))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1099,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1096])).

tff(c_1102,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1099])).

tff(c_1103,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1106,plain,(
    ! [D_197] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_197) = k10_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_46,c_1103])).

tff(c_1071,plain,(
    ! [A_186,B_187,C_188,D_189] :
      ( k7_relset_1(A_186,B_187,C_188,D_189) = k9_relat_1(C_188,D_189)
      | ~ m1_subset_1(C_188,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1074,plain,(
    ! [D_189] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_189) = k9_relat_1('#skF_3',D_189) ),
    inference(resolution,[status(thm)],[c_46,c_1071])).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_682,plain,(
    ! [C_139,A_140,B_141] :
      ( v2_funct_1(C_139)
      | ~ v3_funct_2(C_139,A_140,B_141)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_685,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_682])).

tff(c_688,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_685])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_402,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_406,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_402])).

tff(c_412,plain,(
    ! [B_102,A_103] :
      ( k2_relat_1(B_102) = A_103
      | ~ v2_funct_2(B_102,A_103)
      | ~ v5_relat_1(B_102,A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_415,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_406,c_412])).

tff(c_418,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_415])).

tff(c_419,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_418])).

tff(c_502,plain,(
    ! [C_120,B_121,A_122] :
      ( v2_funct_2(C_120,B_121)
      | ~ v3_funct_2(C_120,A_122,B_121)
      | ~ v1_funct_1(C_120)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_122,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_505,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_502])).

tff(c_508,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_505])).

tff(c_510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_419,c_508])).

tff(c_511,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_418])).

tff(c_14,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_519,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_14])).

tff(c_525,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_519])).

tff(c_666,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k8_relset_1(A_134,B_135,C_136,D_137) = k10_relat_1(C_136,D_137)
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_669,plain,(
    ! [D_137] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_137) = k10_relat_1('#skF_3',D_137) ),
    inference(resolution,[status(thm)],[c_46,c_666])).

tff(c_773,plain,(
    ! [B_151,A_152,C_153] :
      ( k1_xboole_0 = B_151
      | k8_relset_1(A_152,B_151,C_153,B_151) = A_152
      | ~ m1_subset_1(C_153,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151)))
      | ~ v1_funct_2(C_153,A_152,B_151)
      | ~ v1_funct_1(C_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_775,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_773])).

tff(c_778,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_525,c_669,c_775])).

tff(c_779,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_778])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k10_relat_1(B_13,k9_relat_1(B_13,A_12)) = A_12
      | ~ v2_funct_1(B_13)
      | ~ r1_tarski(A_12,k1_relat_1(B_13))
      | ~ v1_funct_1(B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_787,plain,(
    ! [A_12] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_12)) = A_12
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_12,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_18])).

tff(c_816,plain,(
    ! [A_154] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_154)) = A_154
      | ~ r1_tarski(A_154,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_52,c_688,c_787])).

tff(c_593,plain,(
    ! [A_127,B_128,C_129,D_130] :
      ( k7_relset_1(A_127,B_128,C_129,D_130) = k9_relat_1(C_129,D_130)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_596,plain,(
    ! [D_130] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_130) = k9_relat_1('#skF_3',D_130) ),
    inference(resolution,[status(thm)],[c_46,c_593])).

tff(c_85,plain,(
    ! [B_40,A_41] :
      ( v1_relat_1(B_40)
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_41))
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_88,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_46,c_85])).

tff(c_91,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_101,plain,(
    ! [C_43,B_44,A_45] :
      ( v5_relat_1(C_43,B_44)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_45,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_105,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_101])).

tff(c_112,plain,(
    ! [B_50,A_51] :
      ( k2_relat_1(B_50) = A_51
      | ~ v2_funct_2(B_50,A_51)
      | ~ v5_relat_1(B_50,A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_115,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_105,c_112])).

tff(c_118,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_115])).

tff(c_119,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_118])).

tff(c_184,plain,(
    ! [C_69,B_70,A_71] :
      ( v2_funct_2(C_69,B_70)
      | ~ v3_funct_2(C_69,A_71,B_70)
      | ~ v1_funct_1(C_69)
      | ~ m1_subset_1(C_69,k1_zfmisc_1(k2_zfmisc_1(A_71,B_70))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_187,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_184])).

tff(c_190,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_187])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_190])).

tff(c_193,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_118])).

tff(c_214,plain,(
    ! [B_72,A_73] :
      ( k9_relat_1(B_72,k10_relat_1(B_72,A_73)) = A_73
      | ~ r1_tarski(A_73,k2_relat_1(B_72))
      | ~ v1_funct_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_216,plain,(
    ! [A_73] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_73)) = A_73
      | ~ r1_tarski(A_73,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_214])).

tff(c_224,plain,(
    ! [A_73] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_73)) = A_73
      | ~ r1_tarski(A_73,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_52,c_216])).

tff(c_344,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k7_relset_1(A_86,B_87,C_88,D_89) = k9_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_347,plain,(
    ! [D_89] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_89) = k9_relat_1('#skF_3',D_89) ),
    inference(resolution,[status(thm)],[c_46,c_344])).

tff(c_330,plain,(
    ! [A_81,B_82,C_83,D_84] :
      ( k8_relset_1(A_81,B_82,C_83,D_84) = k10_relat_1(C_83,D_84)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_333,plain,(
    ! [D_84] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_84) = k10_relat_1('#skF_3',D_84) ),
    inference(resolution,[status(thm)],[c_46,c_330])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_70,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_334,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_70])).

tff(c_348,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_347,c_334])).

tff(c_360,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_348])).

tff(c_364,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_360])).

tff(c_365,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_597,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_365])).

tff(c_671,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_669,c_597])).

tff(c_830,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_816,c_671])).

tff(c_875,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_830])).

tff(c_876,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_778])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_883,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_876,c_8])).

tff(c_57,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_57])).

tff(c_374,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_890,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_374])).

tff(c_891,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_913,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_891,c_891,c_365])).

tff(c_1075,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1074,c_913])).

tff(c_1108,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_1075])).

tff(c_923,plain,(
    ! [C_157,B_158,A_159] :
      ( v5_relat_1(C_157,B_158)
      | ~ m1_subset_1(C_157,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_927,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_923])).

tff(c_939,plain,(
    ! [B_164,A_165] :
      ( k2_relat_1(B_164) = A_165
      | ~ v2_funct_2(B_164,A_165)
      | ~ v5_relat_1(B_164,A_165)
      | ~ v1_relat_1(B_164) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_942,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_927,c_939])).

tff(c_945,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_942])).

tff(c_946,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_945])).

tff(c_1041,plain,(
    ! [C_183,B_184,A_185] :
      ( v2_funct_2(C_183,B_184)
      | ~ v3_funct_2(C_183,A_185,B_184)
      | ~ v1_funct_1(C_183)
      | ~ m1_subset_1(C_183,k1_zfmisc_1(k2_zfmisc_1(A_185,B_184))) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1044,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1041])).

tff(c_1047,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_1044])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_946,c_1047])).

tff(c_1050,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_945])).

tff(c_1058,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1050,c_14])).

tff(c_1064,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_1058])).

tff(c_1286,plain,(
    ! [B_214,A_215,C_216] :
      ( k1_xboole_0 = B_214
      | k8_relset_1(A_215,B_214,C_216,B_214) = A_215
      | ~ m1_subset_1(C_216,k1_zfmisc_1(k2_zfmisc_1(A_215,B_214)))
      | ~ v1_funct_2(C_216,A_215,B_214)
      | ~ v1_funct_1(C_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1288,plain,
    ( k1_xboole_0 = '#skF_1'
    | k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_1') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_1286])).

tff(c_1291,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_1064,c_1106,c_1288])).

tff(c_1292,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1291])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1237,plain,(
    ! [B_208,A_209] :
      ( k10_relat_1(B_208,k9_relat_1(B_208,A_209)) = A_209
      | ~ v2_funct_1(B_208)
      | ~ r1_tarski(A_209,k1_relat_1(B_208))
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1244,plain,(
    ! [B_208] :
      ( k10_relat_1(B_208,k9_relat_1(B_208,k1_relat_1(B_208))) = k1_relat_1(B_208)
      | ~ v2_funct_1(B_208)
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_6,c_1237])).

tff(c_1298,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1292,c_1244])).

tff(c_1307,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_52,c_1102,c_1292,c_1298])).

tff(c_1309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1108,c_1307])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1291])).

tff(c_1245,plain,(
    ! [B_208] :
      ( k10_relat_1(B_208,k9_relat_1(B_208,k1_xboole_0)) = k1_xboole_0
      | ~ v2_funct_1(B_208)
      | ~ v1_funct_1(B_208)
      | ~ v1_relat_1(B_208) ) ),
    inference(resolution,[status(thm)],[c_8,c_1237])).

tff(c_1375,plain,(
    ! [B_220] :
      ( k10_relat_1(B_220,k9_relat_1(B_220,'#skF_1')) = '#skF_1'
      | ~ v2_funct_1(B_220)
      | ~ v1_funct_1(B_220)
      | ~ v1_relat_1(B_220) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_1310,c_1245])).

tff(c_1385,plain,
    ( ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_1108])).

tff(c_1396,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_373,c_52,c_1102,c_1385])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:28:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/2.84  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/2.87  
% 4.28/2.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/2.87  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.28/2.87  
% 4.28/2.87  %Foreground sorts:
% 4.28/2.87  
% 4.28/2.87  
% 4.28/2.87  %Background operators:
% 4.28/2.87  
% 4.28/2.87  
% 4.28/2.87  %Foreground operators:
% 4.28/2.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.28/2.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.28/2.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.28/2.87  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.28/2.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.28/2.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.28/2.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.28/2.87  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.28/2.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.28/2.87  tff('#skF_2', type, '#skF_2': $i).
% 4.28/2.87  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.28/2.87  tff('#skF_3', type, '#skF_3': $i).
% 4.28/2.87  tff('#skF_1', type, '#skF_1': $i).
% 4.28/2.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.28/2.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.28/2.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.28/2.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.28/2.87  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.28/2.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.28/2.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.28/2.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.28/2.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.28/2.87  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.28/2.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.28/2.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.28/2.87  
% 4.42/2.91  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.42/2.91  tff(f_125, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 4.42/2.91  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.42/2.91  tff(f_90, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.42/2.91  tff(f_78, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.42/2.91  tff(f_74, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.42/2.91  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.42/2.91  tff(f_98, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.42/2.91  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.42/2.91  tff(f_110, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k8_relset_1(A, B, C, B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_funct_2)).
% 4.42/2.91  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.42/2.91  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 4.42/2.91  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.42/2.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.42/2.91  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.42/2.91  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.91  tff(c_367, plain, (![B_91, A_92]: (v1_relat_1(B_91) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)) | ~v1_relat_1(A_92))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.42/2.91  tff(c_370, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_367])).
% 4.42/2.91  tff(c_373, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_370])).
% 4.42/2.91  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.91  tff(c_48, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.91  tff(c_1096, plain, (![C_191, A_192, B_193]: (v2_funct_1(C_191) | ~v3_funct_2(C_191, A_192, B_193) | ~v1_funct_1(C_191) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_192, B_193))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/2.91  tff(c_1099, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1096])).
% 4.42/2.91  tff(c_1102, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1099])).
% 4.42/2.91  tff(c_1103, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.42/2.91  tff(c_1106, plain, (![D_197]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_197)=k10_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_46, c_1103])).
% 4.42/2.91  tff(c_1071, plain, (![A_186, B_187, C_188, D_189]: (k7_relset_1(A_186, B_187, C_188, D_189)=k9_relat_1(C_188, D_189) | ~m1_subset_1(C_188, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.42/2.91  tff(c_1074, plain, (![D_189]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_189)=k9_relat_1('#skF_3', D_189))), inference(resolution, [status(thm)], [c_46, c_1071])).
% 4.42/2.91  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.91  tff(c_682, plain, (![C_139, A_140, B_141]: (v2_funct_1(C_139) | ~v3_funct_2(C_139, A_140, B_141) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/2.91  tff(c_685, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_682])).
% 4.42/2.91  tff(c_688, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_685])).
% 4.42/2.91  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.91  tff(c_402, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/2.91  tff(c_406, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_402])).
% 4.42/2.91  tff(c_412, plain, (![B_102, A_103]: (k2_relat_1(B_102)=A_103 | ~v2_funct_2(B_102, A_103) | ~v5_relat_1(B_102, A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/2.91  tff(c_415, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_406, c_412])).
% 4.42/2.91  tff(c_418, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_415])).
% 4.42/2.91  tff(c_419, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_418])).
% 4.42/2.91  tff(c_502, plain, (![C_120, B_121, A_122]: (v2_funct_2(C_120, B_121) | ~v3_funct_2(C_120, A_122, B_121) | ~v1_funct_1(C_120) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_122, B_121))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/2.91  tff(c_505, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_502])).
% 4.42/2.91  tff(c_508, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_505])).
% 4.42/2.91  tff(c_510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_419, c_508])).
% 4.42/2.91  tff(c_511, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_418])).
% 4.42/2.91  tff(c_14, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.42/2.91  tff(c_519, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_511, c_14])).
% 4.42/2.91  tff(c_525, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_519])).
% 4.42/2.91  tff(c_666, plain, (![A_134, B_135, C_136, D_137]: (k8_relset_1(A_134, B_135, C_136, D_137)=k10_relat_1(C_136, D_137) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.42/2.92  tff(c_669, plain, (![D_137]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_137)=k10_relat_1('#skF_3', D_137))), inference(resolution, [status(thm)], [c_46, c_666])).
% 4.42/2.92  tff(c_773, plain, (![B_151, A_152, C_153]: (k1_xboole_0=B_151 | k8_relset_1(A_152, B_151, C_153, B_151)=A_152 | ~m1_subset_1(C_153, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))) | ~v1_funct_2(C_153, A_152, B_151) | ~v1_funct_1(C_153))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.42/2.92  tff(c_775, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_773])).
% 4.42/2.92  tff(c_778, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_525, c_669, c_775])).
% 4.42/2.92  tff(c_779, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_778])).
% 4.42/2.92  tff(c_18, plain, (![B_13, A_12]: (k10_relat_1(B_13, k9_relat_1(B_13, A_12))=A_12 | ~v2_funct_1(B_13) | ~r1_tarski(A_12, k1_relat_1(B_13)) | ~v1_funct_1(B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.42/2.92  tff(c_787, plain, (![A_12]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_12))=A_12 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_12, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_779, c_18])).
% 4.42/2.92  tff(c_816, plain, (![A_154]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_154))=A_154 | ~r1_tarski(A_154, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_373, c_52, c_688, c_787])).
% 4.42/2.92  tff(c_593, plain, (![A_127, B_128, C_129, D_130]: (k7_relset_1(A_127, B_128, C_129, D_130)=k9_relat_1(C_129, D_130) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.42/2.92  tff(c_596, plain, (![D_130]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_130)=k9_relat_1('#skF_3', D_130))), inference(resolution, [status(thm)], [c_46, c_593])).
% 4.42/2.92  tff(c_85, plain, (![B_40, A_41]: (v1_relat_1(B_40) | ~m1_subset_1(B_40, k1_zfmisc_1(A_41)) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.42/2.92  tff(c_88, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_46, c_85])).
% 4.42/2.92  tff(c_91, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_88])).
% 4.42/2.92  tff(c_101, plain, (![C_43, B_44, A_45]: (v5_relat_1(C_43, B_44) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_45, B_44))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/2.92  tff(c_105, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_101])).
% 4.42/2.92  tff(c_112, plain, (![B_50, A_51]: (k2_relat_1(B_50)=A_51 | ~v2_funct_2(B_50, A_51) | ~v5_relat_1(B_50, A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/2.92  tff(c_115, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_105, c_112])).
% 4.42/2.92  tff(c_118, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_115])).
% 4.42/2.92  tff(c_119, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_118])).
% 4.42/2.92  tff(c_184, plain, (![C_69, B_70, A_71]: (v2_funct_2(C_69, B_70) | ~v3_funct_2(C_69, A_71, B_70) | ~v1_funct_1(C_69) | ~m1_subset_1(C_69, k1_zfmisc_1(k2_zfmisc_1(A_71, B_70))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/2.92  tff(c_187, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_184])).
% 4.42/2.92  tff(c_190, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_187])).
% 4.42/2.92  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119, c_190])).
% 4.42/2.92  tff(c_193, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_118])).
% 4.42/2.92  tff(c_214, plain, (![B_72, A_73]: (k9_relat_1(B_72, k10_relat_1(B_72, A_73))=A_73 | ~r1_tarski(A_73, k2_relat_1(B_72)) | ~v1_funct_1(B_72) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.42/2.92  tff(c_216, plain, (![A_73]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_73))=A_73 | ~r1_tarski(A_73, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_193, c_214])).
% 4.42/2.92  tff(c_224, plain, (![A_73]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_73))=A_73 | ~r1_tarski(A_73, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_52, c_216])).
% 4.42/2.92  tff(c_344, plain, (![A_86, B_87, C_88, D_89]: (k7_relset_1(A_86, B_87, C_88, D_89)=k9_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.42/2.92  tff(c_347, plain, (![D_89]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_89)=k9_relat_1('#skF_3', D_89))), inference(resolution, [status(thm)], [c_46, c_344])).
% 4.42/2.92  tff(c_330, plain, (![A_81, B_82, C_83, D_84]: (k8_relset_1(A_81, B_82, C_83, D_84)=k10_relat_1(C_83, D_84) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.42/2.92  tff(c_333, plain, (![D_84]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_84)=k10_relat_1('#skF_3', D_84))), inference(resolution, [status(thm)], [c_46, c_330])).
% 4.42/2.92  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.42/2.92  tff(c_70, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 4.42/2.92  tff(c_334, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_333, c_70])).
% 4.42/2.92  tff(c_348, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_347, c_334])).
% 4.42/2.92  tff(c_360, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_224, c_348])).
% 4.42/2.92  tff(c_364, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_360])).
% 4.42/2.92  tff(c_365, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 4.42/2.92  tff(c_597, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_365])).
% 4.42/2.92  tff(c_671, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_669, c_597])).
% 4.42/2.92  tff(c_830, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_816, c_671])).
% 4.42/2.92  tff(c_875, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_830])).
% 4.42/2.92  tff(c_876, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_778])).
% 4.42/2.92  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.42/2.92  tff(c_883, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_876, c_8])).
% 4.42/2.92  tff(c_57, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/2.92  tff(c_69, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_57])).
% 4.42/2.92  tff(c_374, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_69])).
% 4.42/2.92  tff(c_890, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_883, c_374])).
% 4.42/2.92  tff(c_891, plain, ('#skF_2'='#skF_1'), inference(splitRight, [status(thm)], [c_69])).
% 4.42/2.92  tff(c_913, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_891, c_891, c_365])).
% 4.42/2.92  tff(c_1075, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1074, c_913])).
% 4.42/2.92  tff(c_1108, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1106, c_1075])).
% 4.42/2.92  tff(c_923, plain, (![C_157, B_158, A_159]: (v5_relat_1(C_157, B_158) | ~m1_subset_1(C_157, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.42/2.92  tff(c_927, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_923])).
% 4.42/2.92  tff(c_939, plain, (![B_164, A_165]: (k2_relat_1(B_164)=A_165 | ~v2_funct_2(B_164, A_165) | ~v5_relat_1(B_164, A_165) | ~v1_relat_1(B_164))), inference(cnfTransformation, [status(thm)], [f_98])).
% 4.42/2.92  tff(c_942, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_927, c_939])).
% 4.42/2.92  tff(c_945, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_942])).
% 4.42/2.92  tff(c_946, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_945])).
% 4.42/2.92  tff(c_1041, plain, (![C_183, B_184, A_185]: (v2_funct_2(C_183, B_184) | ~v3_funct_2(C_183, A_185, B_184) | ~v1_funct_1(C_183) | ~m1_subset_1(C_183, k1_zfmisc_1(k2_zfmisc_1(A_185, B_184))))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.42/2.92  tff(c_1044, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1041])).
% 4.42/2.92  tff(c_1047, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_1044])).
% 4.42/2.92  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_946, c_1047])).
% 4.42/2.92  tff(c_1050, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_945])).
% 4.42/2.92  tff(c_1058, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1050, c_14])).
% 4.42/2.92  tff(c_1064, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_373, c_1058])).
% 4.42/2.92  tff(c_1286, plain, (![B_214, A_215, C_216]: (k1_xboole_0=B_214 | k8_relset_1(A_215, B_214, C_216, B_214)=A_215 | ~m1_subset_1(C_216, k1_zfmisc_1(k2_zfmisc_1(A_215, B_214))) | ~v1_funct_2(C_216, A_215, B_214) | ~v1_funct_1(C_216))), inference(cnfTransformation, [status(thm)], [f_110])).
% 4.42/2.92  tff(c_1288, plain, (k1_xboole_0='#skF_1' | k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_1')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_1286])).
% 4.42/2.92  tff(c_1291, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_1064, c_1106, c_1288])).
% 4.42/2.92  tff(c_1292, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_1291])).
% 4.42/2.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.42/2.92  tff(c_1237, plain, (![B_208, A_209]: (k10_relat_1(B_208, k9_relat_1(B_208, A_209))=A_209 | ~v2_funct_1(B_208) | ~r1_tarski(A_209, k1_relat_1(B_208)) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.42/2.92  tff(c_1244, plain, (![B_208]: (k10_relat_1(B_208, k9_relat_1(B_208, k1_relat_1(B_208)))=k1_relat_1(B_208) | ~v2_funct_1(B_208) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_6, c_1237])).
% 4.42/2.92  tff(c_1298, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1292, c_1244])).
% 4.42/2.92  tff(c_1307, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_373, c_52, c_1102, c_1292, c_1298])).
% 4.42/2.92  tff(c_1309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1108, c_1307])).
% 4.42/2.92  tff(c_1310, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_1291])).
% 4.42/2.92  tff(c_1245, plain, (![B_208]: (k10_relat_1(B_208, k9_relat_1(B_208, k1_xboole_0))=k1_xboole_0 | ~v2_funct_1(B_208) | ~v1_funct_1(B_208) | ~v1_relat_1(B_208))), inference(resolution, [status(thm)], [c_8, c_1237])).
% 4.42/2.92  tff(c_1375, plain, (![B_220]: (k10_relat_1(B_220, k9_relat_1(B_220, '#skF_1'))='#skF_1' | ~v2_funct_1(B_220) | ~v1_funct_1(B_220) | ~v1_relat_1(B_220))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_1310, c_1245])).
% 4.42/2.92  tff(c_1385, plain, (~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1375, c_1108])).
% 4.42/2.92  tff(c_1396, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_373, c_52, c_1102, c_1385])).
% 4.42/2.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.42/2.92  
% 4.42/2.92  Inference rules
% 4.42/2.92  ----------------------
% 4.42/2.92  #Ref     : 0
% 4.42/2.92  #Sup     : 290
% 4.42/2.92  #Fact    : 0
% 4.42/2.92  #Define  : 0
% 4.42/2.92  #Split   : 8
% 4.42/2.92  #Chain   : 0
% 4.42/2.92  #Close   : 0
% 4.42/2.92  
% 4.42/2.92  Ordering : KBO
% 4.42/2.92  
% 4.42/2.92  Simplification rules
% 4.42/2.92  ----------------------
% 4.42/2.92  #Subsume      : 4
% 4.42/2.92  #Demod        : 320
% 4.42/2.92  #Tautology    : 202
% 4.42/2.92  #SimpNegUnit  : 4
% 4.42/2.92  #BackRed      : 37
% 4.42/2.92  
% 4.42/2.92  #Partial instantiations: 0
% 4.42/2.92  #Strategies tried      : 1
% 4.42/2.92  
% 4.42/2.92  Timing (in seconds)
% 4.42/2.92  ----------------------
% 4.42/2.92  Preprocessing        : 0.74
% 4.42/2.92  Parsing              : 0.40
% 4.42/2.92  CNF conversion       : 0.06
% 4.42/2.92  Main loop            : 1.05
% 4.42/2.92  Inferencing          : 0.39
% 4.42/2.92  Reduction            : 0.39
% 4.42/2.92  Demodulation         : 0.29
% 4.42/2.92  BG Simplification    : 0.05
% 4.42/2.92  Subsumption          : 0.16
% 4.42/2.92  Abstraction          : 0.07
% 4.42/2.92  MUC search           : 0.00
% 4.42/2.92  Cooper               : 0.00
% 4.42/2.92  Total                : 1.88
% 4.42/2.92  Index Insertion      : 0.00
% 4.42/2.92  Index Deletion       : 0.00
% 4.42/2.92  Index Matching       : 0.00
% 4.42/2.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
