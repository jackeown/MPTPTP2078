%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 2.66s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 236 expanded)
%              Number of leaves         :   37 (  99 expanded)
%              Depth                    :    9
%              Number of atoms          :  156 ( 664 expanded)
%              Number of equality atoms :   55 ( 234 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_95,axiom,(
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

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_61,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(c_42,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_44,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_51,plain,(
    ! [C_30,A_31,B_32] :
      ( v1_relat_1(C_30)
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_55,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_51])).

tff(c_50,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_46,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_395,plain,(
    ! [C_139,A_140,B_141] :
      ( v2_funct_1(C_139)
      | ~ v3_funct_2(C_139,A_140,B_141)
      | ~ v1_funct_1(C_139)
      | ~ m1_subset_1(C_139,k1_zfmisc_1(k2_zfmisc_1(A_140,B_141))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_398,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_395])).

tff(c_401,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_398])).

tff(c_48,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_314,plain,(
    ! [A_121,B_122,C_123] :
      ( k1_relset_1(A_121,B_122,C_123) = k1_relat_1(C_123)
      | ~ m1_subset_1(C_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_318,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_314])).

tff(c_418,plain,(
    ! [B_154,A_155,C_156] :
      ( k1_xboole_0 = B_154
      | k1_relset_1(A_155,B_154,C_156) = A_155
      | ~ v1_funct_2(C_156,A_155,B_154)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_155,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_421,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_418])).

tff(c_424,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_318,c_421])).

tff(c_425,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_424])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( k10_relat_1(B_4,k9_relat_1(B_4,A_3)) = A_3
      | ~ v2_funct_1(B_4)
      | ~ r1_tarski(A_3,k1_relat_1(B_4))
      | ~ v1_funct_1(B_4)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_429,plain,(
    ! [A_3] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_3)) = A_3
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_3,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_4])).

tff(c_439,plain,(
    ! [A_157] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_157)) = A_157
      | ~ r1_tarski(A_157,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_50,c_401,c_429])).

tff(c_343,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k7_relset_1(A_129,B_130,C_131,D_132) = k9_relat_1(C_131,D_132)
      | ~ m1_subset_1(C_131,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_346,plain,(
    ! [D_132] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_132) = k9_relat_1('#skF_3',D_132) ),
    inference(resolution,[status(thm)],[c_44,c_343])).

tff(c_324,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( k8_relset_1(A_124,B_125,C_126,D_127) = k10_relat_1(C_126,D_127)
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_327,plain,(
    ! [D_127] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_127) = k10_relat_1('#skF_3',D_127) ),
    inference(resolution,[status(thm)],[c_44,c_324])).

tff(c_62,plain,(
    ! [C_36,B_37,A_38] :
      ( v5_relat_1(C_36,B_37)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_66,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_62])).

tff(c_68,plain,(
    ! [B_40,A_41] :
      ( k2_relat_1(B_40) = A_41
      | ~ v2_funct_2(B_40,A_41)
      | ~ v5_relat_1(B_40,A_41)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_68])).

tff(c_74,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_71])).

tff(c_76,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_125,plain,(
    ! [C_67,B_68,A_69] :
      ( v2_funct_2(C_67,B_68)
      | ~ v3_funct_2(C_67,A_69,B_68)
      | ~ v1_funct_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_69,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_128,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_131,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_46,c_128])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_131])).

tff(c_134,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_177,plain,(
    ! [B_83,A_84] :
      ( k9_relat_1(B_83,k10_relat_1(B_83,A_84)) = A_84
      | ~ r1_tarski(A_84,k2_relat_1(B_83))
      | ~ v1_funct_1(B_83)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_179,plain,(
    ! [A_84] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_84)) = A_84
      | ~ r1_tarski(A_84,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_177])).

tff(c_196,plain,(
    ! [A_90] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_90)) = A_90
      | ~ r1_tarski(A_90,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_50,c_179])).

tff(c_182,plain,(
    ! [A_85,B_86,C_87,D_88] :
      ( k8_relset_1(A_85,B_86,C_87,D_88) = k10_relat_1(C_87,D_88)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_185,plain,(
    ! [D_88] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_88) = k10_relat_1('#skF_3',D_88) ),
    inference(resolution,[status(thm)],[c_44,c_182])).

tff(c_156,plain,(
    ! [A_75,B_76,C_77,D_78] :
      ( k7_relset_1(A_75,B_76,C_77,D_78) = k9_relat_1(C_77,D_78)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_159,plain,(
    ! [D_78] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_78) = k9_relat_1('#skF_3',D_78) ),
    inference(resolution,[status(thm)],[c_44,c_156])).

tff(c_40,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_61,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_160,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_61])).

tff(c_186,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_160])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_186])).

tff(c_210,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_202])).

tff(c_211,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_329,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_211])).

tff(c_347,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_329])).

tff(c_448,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_347])).

tff(c_463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_448])).

tff(c_465,plain,(
    k1_relat_1('#skF_3') != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_464,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_424])).

tff(c_32,plain,(
    ! [B_26,C_27] :
      ( k1_relset_1(k1_xboole_0,B_26,C_27) = k1_xboole_0
      | ~ v1_funct_2(C_27,k1_xboole_0,B_26)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_491,plain,(
    ! [B_163,C_164] :
      ( k1_relset_1('#skF_1',B_163,C_164) = '#skF_1'
      | ~ v1_funct_2(C_164,'#skF_1',B_163)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_163))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_464,c_464,c_464,c_464,c_32])).

tff(c_494,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_491])).

tff(c_497,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_318,c_494])).

tff(c_499,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_465,c_497])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n010.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:07:14 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.66/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.49  
% 2.66/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.49  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.66/1.49  
% 2.66/1.49  %Foreground sorts:
% 2.66/1.49  
% 2.66/1.49  
% 2.66/1.49  %Background operators:
% 2.66/1.49  
% 2.66/1.49  
% 2.66/1.49  %Foreground operators:
% 2.66/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.66/1.49  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.66/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.66/1.49  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.66/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.66/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.66/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.66/1.49  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.66/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.66/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.66/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.66/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.66/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.66/1.49  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.66/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.66/1.49  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.66/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.66/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.66/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.66/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.66/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.66/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.66/1.49  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.66/1.49  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.66/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.66/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.66/1.49  
% 2.83/1.51  tff(f_118, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 2.83/1.51  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.83/1.51  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.83/1.51  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.83/1.51  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.83/1.51  tff(f_43, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 2.83/1.51  tff(f_61, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.83/1.51  tff(f_65, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.83/1.51  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.83/1.51  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 2.83/1.51  tff(f_33, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 2.83/1.51  tff(c_42, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_44, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_51, plain, (![C_30, A_31, B_32]: (v1_relat_1(C_30) | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.83/1.51  tff(c_55, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_51])).
% 2.83/1.51  tff(c_50, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_46, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_395, plain, (![C_139, A_140, B_141]: (v2_funct_1(C_139) | ~v3_funct_2(C_139, A_140, B_141) | ~v1_funct_1(C_139) | ~m1_subset_1(C_139, k1_zfmisc_1(k2_zfmisc_1(A_140, B_141))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.83/1.51  tff(c_398, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_395])).
% 2.83/1.51  tff(c_401, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_398])).
% 2.83/1.51  tff(c_48, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_314, plain, (![A_121, B_122, C_123]: (k1_relset_1(A_121, B_122, C_123)=k1_relat_1(C_123) | ~m1_subset_1(C_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.83/1.51  tff(c_318, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_314])).
% 2.83/1.51  tff(c_418, plain, (![B_154, A_155, C_156]: (k1_xboole_0=B_154 | k1_relset_1(A_155, B_154, C_156)=A_155 | ~v1_funct_2(C_156, A_155, B_154) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_155, B_154))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.51  tff(c_421, plain, (k1_xboole_0='#skF_1' | k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_418])).
% 2.83/1.51  tff(c_424, plain, (k1_xboole_0='#skF_1' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_318, c_421])).
% 2.83/1.51  tff(c_425, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitLeft, [status(thm)], [c_424])).
% 2.83/1.51  tff(c_4, plain, (![B_4, A_3]: (k10_relat_1(B_4, k9_relat_1(B_4, A_3))=A_3 | ~v2_funct_1(B_4) | ~r1_tarski(A_3, k1_relat_1(B_4)) | ~v1_funct_1(B_4) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.83/1.51  tff(c_429, plain, (![A_3]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_3))=A_3 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_3, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_4])).
% 2.83/1.51  tff(c_439, plain, (![A_157]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_157))=A_157 | ~r1_tarski(A_157, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_50, c_401, c_429])).
% 2.83/1.51  tff(c_343, plain, (![A_129, B_130, C_131, D_132]: (k7_relset_1(A_129, B_130, C_131, D_132)=k9_relat_1(C_131, D_132) | ~m1_subset_1(C_131, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.51  tff(c_346, plain, (![D_132]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_132)=k9_relat_1('#skF_3', D_132))), inference(resolution, [status(thm)], [c_44, c_343])).
% 2.83/1.51  tff(c_324, plain, (![A_124, B_125, C_126, D_127]: (k8_relset_1(A_124, B_125, C_126, D_127)=k10_relat_1(C_126, D_127) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.51  tff(c_327, plain, (![D_127]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_127)=k10_relat_1('#skF_3', D_127))), inference(resolution, [status(thm)], [c_44, c_324])).
% 2.83/1.51  tff(c_62, plain, (![C_36, B_37, A_38]: (v5_relat_1(C_36, B_37) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.83/1.51  tff(c_66, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_62])).
% 2.83/1.51  tff(c_68, plain, (![B_40, A_41]: (k2_relat_1(B_40)=A_41 | ~v2_funct_2(B_40, A_41) | ~v5_relat_1(B_40, A_41) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.83/1.51  tff(c_71, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_68])).
% 2.83/1.51  tff(c_74, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55, c_71])).
% 2.83/1.51  tff(c_76, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_74])).
% 2.83/1.51  tff(c_125, plain, (![C_67, B_68, A_69]: (v2_funct_2(C_67, B_68) | ~v3_funct_2(C_67, A_69, B_68) | ~v1_funct_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_69, B_68))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.83/1.51  tff(c_128, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_44, c_125])).
% 2.83/1.51  tff(c_131, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_46, c_128])).
% 2.83/1.51  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_131])).
% 2.83/1.51  tff(c_134, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_74])).
% 2.83/1.51  tff(c_177, plain, (![B_83, A_84]: (k9_relat_1(B_83, k10_relat_1(B_83, A_84))=A_84 | ~r1_tarski(A_84, k2_relat_1(B_83)) | ~v1_funct_1(B_83) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.83/1.51  tff(c_179, plain, (![A_84]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_84))=A_84 | ~r1_tarski(A_84, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_177])).
% 2.83/1.51  tff(c_196, plain, (![A_90]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_90))=A_90 | ~r1_tarski(A_90, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_50, c_179])).
% 2.83/1.51  tff(c_182, plain, (![A_85, B_86, C_87, D_88]: (k8_relset_1(A_85, B_86, C_87, D_88)=k10_relat_1(C_87, D_88) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.83/1.51  tff(c_185, plain, (![D_88]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_88)=k10_relat_1('#skF_3', D_88))), inference(resolution, [status(thm)], [c_44, c_182])).
% 2.83/1.51  tff(c_156, plain, (![A_75, B_76, C_77, D_78]: (k7_relset_1(A_75, B_76, C_77, D_78)=k9_relat_1(C_77, D_78) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.83/1.51  tff(c_159, plain, (![D_78]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_78)=k9_relat_1('#skF_3', D_78))), inference(resolution, [status(thm)], [c_44, c_156])).
% 2.83/1.51  tff(c_40, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.83/1.51  tff(c_61, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 2.83/1.51  tff(c_160, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_61])).
% 2.83/1.51  tff(c_186, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_160])).
% 2.83/1.51  tff(c_202, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_196, c_186])).
% 2.83/1.51  tff(c_210, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_202])).
% 2.83/1.51  tff(c_211, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 2.83/1.51  tff(c_329, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_327, c_211])).
% 2.83/1.51  tff(c_347, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_346, c_329])).
% 2.83/1.51  tff(c_448, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_439, c_347])).
% 2.83/1.51  tff(c_463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_448])).
% 2.83/1.51  tff(c_465, plain, (k1_relat_1('#skF_3')!='#skF_1'), inference(splitRight, [status(thm)], [c_424])).
% 2.83/1.51  tff(c_464, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_424])).
% 2.83/1.51  tff(c_32, plain, (![B_26, C_27]: (k1_relset_1(k1_xboole_0, B_26, C_27)=k1_xboole_0 | ~v1_funct_2(C_27, k1_xboole_0, B_26) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.83/1.51  tff(c_491, plain, (![B_163, C_164]: (k1_relset_1('#skF_1', B_163, C_164)='#skF_1' | ~v1_funct_2(C_164, '#skF_1', B_163) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_163))))), inference(demodulation, [status(thm), theory('equality')], [c_464, c_464, c_464, c_464, c_32])).
% 2.83/1.51  tff(c_494, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_44, c_491])).
% 2.83/1.51  tff(c_497, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_318, c_494])).
% 2.83/1.51  tff(c_499, plain, $false, inference(negUnitSimplification, [status(thm)], [c_465, c_497])).
% 2.83/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.83/1.51  
% 2.83/1.51  Inference rules
% 2.83/1.51  ----------------------
% 2.83/1.51  #Ref     : 0
% 2.83/1.51  #Sup     : 96
% 2.83/1.51  #Fact    : 0
% 2.83/1.51  #Define  : 0
% 2.83/1.51  #Split   : 4
% 2.83/1.51  #Chain   : 0
% 2.83/1.51  #Close   : 0
% 2.83/1.51  
% 2.83/1.51  Ordering : KBO
% 2.83/1.51  
% 2.83/1.51  Simplification rules
% 2.83/1.51  ----------------------
% 2.83/1.51  #Subsume      : 1
% 2.83/1.51  #Demod        : 77
% 2.83/1.51  #Tautology    : 59
% 2.83/1.51  #SimpNegUnit  : 3
% 2.83/1.51  #BackRed      : 17
% 2.83/1.51  
% 2.83/1.51  #Partial instantiations: 0
% 2.83/1.51  #Strategies tried      : 1
% 2.83/1.51  
% 2.83/1.51  Timing (in seconds)
% 2.83/1.51  ----------------------
% 2.83/1.51  Preprocessing        : 0.41
% 2.83/1.51  Parsing              : 0.22
% 2.83/1.51  CNF conversion       : 0.02
% 2.83/1.51  Main loop            : 0.27
% 2.83/1.51  Inferencing          : 0.11
% 2.83/1.51  Reduction            : 0.08
% 2.83/1.51  Demodulation         : 0.06
% 2.83/1.51  BG Simplification    : 0.02
% 2.83/1.51  Subsumption          : 0.04
% 2.83/1.51  Abstraction          : 0.01
% 2.83/1.51  MUC search           : 0.00
% 2.83/1.51  Cooper               : 0.00
% 2.83/1.51  Total                : 0.71
% 2.83/1.51  Index Insertion      : 0.00
% 2.83/1.51  Index Deletion       : 0.00
% 2.83/1.51  Index Matching       : 0.00
% 2.83/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
