%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:10 EST 2020

% Result     : Theorem 2.46s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 273 expanded)
%              Number of leaves         :   33 ( 103 expanded)
%              Depth                    :   12
%              Number of atoms          :  149 ( 560 expanded)
%              Number of equality atoms :   27 (  83 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_102,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_63,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_36,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_690,plain,(
    ! [A_164,B_165,C_166] :
      ( k1_relset_1(A_164,B_165,C_166) = k1_relat_1(C_166)
      | ~ m1_subset_1(C_166,k1_zfmisc_1(k2_zfmisc_1(A_164,B_165))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_699,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_690])).

tff(c_34,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_700,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_699,c_34])).

tff(c_93,plain,(
    ! [C_52,A_53,B_54] :
      ( v1_relat_1(C_52)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_102,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_93])).

tff(c_161,plain,(
    ! [C_71,B_72,A_73] :
      ( v5_relat_1(C_71,B_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_73,B_72))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_170,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_161])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_293,plain,(
    ! [A_103,B_104,C_105] :
      ( k2_relset_1(A_103,B_104,C_105) = k2_relat_1(C_105)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_103,B_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_307,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_293])).

tff(c_18,plain,(
    ! [A_13] :
      ( v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_42] :
      ( v1_xboole_0(k1_relat_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [A_43] :
      ( k1_relat_1(A_43) = k1_xboole_0
      | ~ v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_64,plain,(
    ! [A_46] :
      ( k1_relat_1(k1_relat_1(A_46)) = k1_xboole_0
      | ~ v1_xboole_0(A_46) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_73,plain,(
    ! [A_46] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_46))
      | ~ v1_xboole_0(A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_18])).

tff(c_111,plain,(
    ! [A_58] :
      ( ~ v1_xboole_0(k1_relat_1(A_58))
      | ~ v1_xboole_0(A_58) ) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_118,plain,(
    ! [A_13] : ~ v1_xboole_0(A_13) ),
    inference(resolution,[status(thm)],[c_18,c_111])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_120,plain,(
    ! [A_1] : r2_hidden('#skF_1'(A_1),A_1) ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_4])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [A_77,C_78,B_79] :
      ( m1_subset_1(A_77,C_78)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(C_78))
      | ~ r2_hidden(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_190,plain,(
    ! [A_81,B_82,A_83] :
      ( m1_subset_1(A_81,B_82)
      | ~ r2_hidden(A_81,A_83)
      | ~ r1_tarski(A_83,B_82) ) ),
    inference(resolution,[status(thm)],[c_10,c_182])).

tff(c_194,plain,(
    ! [A_84,B_85] :
      ( m1_subset_1('#skF_1'(A_84),B_85)
      | ~ r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_120,c_190])).

tff(c_58,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_relset_1('#skF_2','#skF_3','#skF_4'))
      | ~ m1_subset_1(D_45,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_63,plain,
    ( ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3')
    | v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_110,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_220,plain,(
    ~ r1_tarski(k2_relset_1('#skF_2','#skF_3','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_194,c_110])).

tff(c_308,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_220])).

tff(c_317,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_308])).

tff(c_321,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_170,c_317])).

tff(c_322,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_331,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_322,c_6])).

tff(c_332,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_331,c_322])).

tff(c_47,plain,(
    ! [A_42] :
      ( k1_relat_1(A_42) = k1_xboole_0
      | ~ v1_xboole_0(A_42) ) ),
    inference(resolution,[status(thm)],[c_43,c_6])).

tff(c_344,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_332,c_47])).

tff(c_362,plain,(
    ! [A_108] :
      ( ~ v1_xboole_0(k1_relat_1(A_108))
      | ~ v1_xboole_0(A_108) ) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_365,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_362])).

tff(c_374,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_332,c_365])).

tff(c_375,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_489,plain,(
    ! [A_136,B_137,C_138] :
      ( k1_relset_1(A_136,B_137,C_138) = k1_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_498,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_489])).

tff(c_499,plain,(
    k1_relat_1('#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_498,c_34])).

tff(c_419,plain,(
    ! [C_117,B_118,A_119] :
      ( v5_relat_1(C_117,B_118)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(k2_zfmisc_1(A_119,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_428,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_419])).

tff(c_455,plain,(
    ! [A_125,C_126,B_127] :
      ( m1_subset_1(A_125,C_126)
      | ~ m1_subset_1(B_127,k1_zfmisc_1(C_126))
      | ~ r2_hidden(A_125,B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_463,plain,(
    ! [A_129,B_130,A_131] :
      ( m1_subset_1(A_129,B_130)
      | ~ r2_hidden(A_129,A_131)
      | ~ r1_tarski(A_131,B_130) ) ),
    inference(resolution,[status(thm)],[c_10,c_455])).

tff(c_504,plain,(
    ! [A_139,B_140] :
      ( m1_subset_1('#skF_1'(A_139),B_140)
      | ~ r1_tarski(A_139,B_140)
      | v1_xboole_0(A_139) ) ),
    inference(resolution,[status(thm)],[c_4,c_463])).

tff(c_467,plain,(
    ! [A_132,B_133,C_134] :
      ( k2_relset_1(A_132,B_133,C_134) = k2_relat_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_132,B_133))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_476,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_467])).

tff(c_385,plain,(
    ~ m1_subset_1('#skF_1'(k2_relset_1('#skF_2','#skF_3','#skF_4')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_477,plain,(
    ~ m1_subset_1('#skF_1'(k2_relat_1('#skF_4')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_385])).

tff(c_536,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_504,c_477])).

tff(c_543,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_536])).

tff(c_546,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_543])).

tff(c_550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_428,c_546])).

tff(c_551,plain,(
    v1_xboole_0(k2_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_536])).

tff(c_20,plain,(
    ! [A_14] :
      ( ~ v1_xboole_0(k2_relat_1(A_14))
      | ~ v1_relat_1(A_14)
      | v1_xboole_0(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_566,plain,
    ( ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_551,c_20])).

tff(c_575,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_566])).

tff(c_580,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_575,c_47])).

tff(c_587,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_499,c_580])).

tff(c_588,plain,(
    v1_xboole_0(k2_relset_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_611,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_588,c_6])).

tff(c_706,plain,(
    ! [A_168,B_169,C_170] :
      ( k2_relset_1(A_168,B_169,C_170) = k2_relat_1(C_170)
      | ~ m1_subset_1(C_170,k1_zfmisc_1(k2_zfmisc_1(A_168,B_169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_713,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_36,c_706])).

tff(c_716,plain,(
    k2_relat_1('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_611,c_713])).

tff(c_726,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_4')
    | v1_xboole_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_716,c_20])).

tff(c_734,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_375,c_726])).

tff(c_738,plain,(
    k1_relat_1('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_734,c_47])).

tff(c_745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_700,c_738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:41:23 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.46/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  
% 2.76/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.38  %$ v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.76/1.38  
% 2.76/1.38  %Foreground sorts:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Background operators:
% 2.76/1.38  
% 2.76/1.38  
% 2.76/1.38  %Foreground operators:
% 2.76/1.38  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.76/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.76/1.38  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.76/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.76/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.76/1.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.76/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.76/1.38  tff('#skF_3', type, '#skF_3': $i).
% 2.76/1.38  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.76/1.38  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.76/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.76/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.76/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.76/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.76/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.76/1.38  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.76/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.76/1.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.76/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.76/1.38  
% 2.76/1.40  tff(f_102, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ~(~(k1_relset_1(A, B, C) = k1_xboole_0) & (![D]: (m1_subset_1(D, B) => ~r2_hidden(D, k2_relset_1(A, B, C))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_relset_1)).
% 2.76/1.40  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.76/1.40  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.76/1.40  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.76/1.40  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.76/1.40  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.76/1.40  tff(f_55, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.76/1.40  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.76/1.40  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.76/1.40  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.40  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 2.76/1.40  tff(f_63, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 2.76/1.40  tff(c_36, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.40  tff(c_690, plain, (![A_164, B_165, C_166]: (k1_relset_1(A_164, B_165, C_166)=k1_relat_1(C_166) | ~m1_subset_1(C_166, k1_zfmisc_1(k2_zfmisc_1(A_164, B_165))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.76/1.40  tff(c_699, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_690])).
% 2.76/1.40  tff(c_34, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.40  tff(c_700, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_699, c_34])).
% 2.76/1.40  tff(c_93, plain, (![C_52, A_53, B_54]: (v1_relat_1(C_52) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.76/1.40  tff(c_102, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_93])).
% 2.76/1.40  tff(c_161, plain, (![C_71, B_72, A_73]: (v5_relat_1(C_71, B_72) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_73, B_72))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.76/1.40  tff(c_170, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_161])).
% 2.76/1.40  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.40  tff(c_293, plain, (![A_103, B_104, C_105]: (k2_relset_1(A_103, B_104, C_105)=k2_relat_1(C_105) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_103, B_104))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.40  tff(c_307, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_293])).
% 2.76/1.40  tff(c_18, plain, (![A_13]: (v1_xboole_0(k1_relat_1(A_13)) | ~v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.40  tff(c_43, plain, (![A_42]: (v1_xboole_0(k1_relat_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.76/1.40  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.76/1.40  tff(c_48, plain, (![A_43]: (k1_relat_1(A_43)=k1_xboole_0 | ~v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_43, c_6])).
% 2.76/1.40  tff(c_64, plain, (![A_46]: (k1_relat_1(k1_relat_1(A_46))=k1_xboole_0 | ~v1_xboole_0(A_46))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.76/1.40  tff(c_73, plain, (![A_46]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_46)) | ~v1_xboole_0(A_46))), inference(superposition, [status(thm), theory('equality')], [c_64, c_18])).
% 2.76/1.40  tff(c_111, plain, (![A_58]: (~v1_xboole_0(k1_relat_1(A_58)) | ~v1_xboole_0(A_58))), inference(splitLeft, [status(thm)], [c_73])).
% 2.76/1.40  tff(c_118, plain, (![A_13]: (~v1_xboole_0(A_13))), inference(resolution, [status(thm)], [c_18, c_111])).
% 2.76/1.40  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.76/1.40  tff(c_120, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1))), inference(negUnitSimplification, [status(thm)], [c_118, c_4])).
% 2.76/1.40  tff(c_10, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.40  tff(c_182, plain, (![A_77, C_78, B_79]: (m1_subset_1(A_77, C_78) | ~m1_subset_1(B_79, k1_zfmisc_1(C_78)) | ~r2_hidden(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.40  tff(c_190, plain, (![A_81, B_82, A_83]: (m1_subset_1(A_81, B_82) | ~r2_hidden(A_81, A_83) | ~r1_tarski(A_83, B_82))), inference(resolution, [status(thm)], [c_10, c_182])).
% 2.76/1.40  tff(c_194, plain, (![A_84, B_85]: (m1_subset_1('#skF_1'(A_84), B_85) | ~r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_120, c_190])).
% 2.76/1.40  tff(c_58, plain, (![D_45]: (~r2_hidden(D_45, k2_relset_1('#skF_2', '#skF_3', '#skF_4')) | ~m1_subset_1(D_45, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.76/1.40  tff(c_63, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3') | v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.76/1.40  tff(c_110, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.76/1.40  tff(c_220, plain, (~r1_tarski(k2_relset_1('#skF_2', '#skF_3', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_194, c_110])).
% 2.76/1.40  tff(c_308, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_307, c_220])).
% 2.76/1.40  tff(c_317, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_308])).
% 2.76/1.40  tff(c_321, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_170, c_317])).
% 2.76/1.40  tff(c_322, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.76/1.40  tff(c_331, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_322, c_6])).
% 2.76/1.40  tff(c_332, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_331, c_322])).
% 2.76/1.40  tff(c_47, plain, (![A_42]: (k1_relat_1(A_42)=k1_xboole_0 | ~v1_xboole_0(A_42))), inference(resolution, [status(thm)], [c_43, c_6])).
% 2.76/1.40  tff(c_344, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_332, c_47])).
% 2.76/1.40  tff(c_362, plain, (![A_108]: (~v1_xboole_0(k1_relat_1(A_108)) | ~v1_xboole_0(A_108))), inference(splitLeft, [status(thm)], [c_73])).
% 2.76/1.40  tff(c_365, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_344, c_362])).
% 2.76/1.40  tff(c_374, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_332, c_332, c_365])).
% 2.76/1.40  tff(c_375, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 2.76/1.40  tff(c_489, plain, (![A_136, B_137, C_138]: (k1_relset_1(A_136, B_137, C_138)=k1_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.76/1.40  tff(c_498, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_489])).
% 2.76/1.40  tff(c_499, plain, (k1_relat_1('#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_498, c_34])).
% 2.76/1.40  tff(c_419, plain, (![C_117, B_118, A_119]: (v5_relat_1(C_117, B_118) | ~m1_subset_1(C_117, k1_zfmisc_1(k2_zfmisc_1(A_119, B_118))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.76/1.40  tff(c_428, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_419])).
% 2.76/1.40  tff(c_455, plain, (![A_125, C_126, B_127]: (m1_subset_1(A_125, C_126) | ~m1_subset_1(B_127, k1_zfmisc_1(C_126)) | ~r2_hidden(A_125, B_127))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.76/1.40  tff(c_463, plain, (![A_129, B_130, A_131]: (m1_subset_1(A_129, B_130) | ~r2_hidden(A_129, A_131) | ~r1_tarski(A_131, B_130))), inference(resolution, [status(thm)], [c_10, c_455])).
% 2.76/1.40  tff(c_504, plain, (![A_139, B_140]: (m1_subset_1('#skF_1'(A_139), B_140) | ~r1_tarski(A_139, B_140) | v1_xboole_0(A_139))), inference(resolution, [status(thm)], [c_4, c_463])).
% 2.76/1.40  tff(c_467, plain, (![A_132, B_133, C_134]: (k2_relset_1(A_132, B_133, C_134)=k2_relat_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_132, B_133))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.40  tff(c_476, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_467])).
% 2.76/1.40  tff(c_385, plain, (~m1_subset_1('#skF_1'(k2_relset_1('#skF_2', '#skF_3', '#skF_4')), '#skF_3')), inference(splitLeft, [status(thm)], [c_63])).
% 2.76/1.40  tff(c_477, plain, (~m1_subset_1('#skF_1'(k2_relat_1('#skF_4')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_476, c_385])).
% 2.76/1.40  tff(c_536, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | v1_xboole_0(k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_504, c_477])).
% 2.76/1.40  tff(c_543, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitLeft, [status(thm)], [c_536])).
% 2.76/1.40  tff(c_546, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_16, c_543])).
% 2.76/1.40  tff(c_550, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_428, c_546])).
% 2.76/1.40  tff(c_551, plain, (v1_xboole_0(k2_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_536])).
% 2.76/1.40  tff(c_20, plain, (![A_14]: (~v1_xboole_0(k2_relat_1(A_14)) | ~v1_relat_1(A_14) | v1_xboole_0(A_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.76/1.40  tff(c_566, plain, (~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_551, c_20])).
% 2.76/1.40  tff(c_575, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_566])).
% 2.76/1.40  tff(c_580, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_575, c_47])).
% 2.76/1.40  tff(c_587, plain, $false, inference(negUnitSimplification, [status(thm)], [c_499, c_580])).
% 2.76/1.40  tff(c_588, plain, (v1_xboole_0(k2_relset_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_63])).
% 2.76/1.40  tff(c_611, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_588, c_6])).
% 2.76/1.40  tff(c_706, plain, (![A_168, B_169, C_170]: (k2_relset_1(A_168, B_169, C_170)=k2_relat_1(C_170) | ~m1_subset_1(C_170, k1_zfmisc_1(k2_zfmisc_1(A_168, B_169))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.76/1.40  tff(c_713, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_36, c_706])).
% 2.76/1.40  tff(c_716, plain, (k2_relat_1('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_611, c_713])).
% 2.76/1.40  tff(c_726, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_4') | v1_xboole_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_716, c_20])).
% 2.76/1.40  tff(c_734, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_375, c_726])).
% 2.76/1.40  tff(c_738, plain, (k1_relat_1('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_734, c_47])).
% 2.76/1.40  tff(c_745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_700, c_738])).
% 2.76/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.40  
% 2.76/1.40  Inference rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Ref     : 0
% 2.76/1.40  #Sup     : 147
% 2.76/1.40  #Fact    : 0
% 2.76/1.40  #Define  : 0
% 2.76/1.40  #Split   : 4
% 2.76/1.40  #Chain   : 0
% 2.76/1.40  #Close   : 0
% 2.76/1.40  
% 2.76/1.40  Ordering : KBO
% 2.76/1.40  
% 2.76/1.40  Simplification rules
% 2.76/1.40  ----------------------
% 2.76/1.40  #Subsume      : 15
% 2.76/1.40  #Demod        : 53
% 2.76/1.40  #Tautology    : 52
% 2.76/1.40  #SimpNegUnit  : 5
% 2.76/1.40  #BackRed      : 13
% 2.76/1.40  
% 2.76/1.40  #Partial instantiations: 0
% 2.76/1.40  #Strategies tried      : 1
% 2.76/1.40  
% 2.76/1.40  Timing (in seconds)
% 2.76/1.40  ----------------------
% 2.76/1.40  Preprocessing        : 0.31
% 2.76/1.40  Parsing              : 0.17
% 2.76/1.40  CNF conversion       : 0.02
% 2.76/1.40  Main loop            : 0.31
% 2.76/1.40  Inferencing          : 0.13
% 2.76/1.40  Reduction            : 0.09
% 2.76/1.40  Demodulation         : 0.06
% 2.76/1.40  BG Simplification    : 0.02
% 2.76/1.40  Subsumption          : 0.05
% 2.76/1.40  Abstraction          : 0.02
% 2.76/1.40  MUC search           : 0.00
% 2.76/1.40  Cooper               : 0.00
% 2.76/1.40  Total                : 0.66
% 2.76/1.40  Index Insertion      : 0.00
% 2.76/1.40  Index Deletion       : 0.00
% 2.76/1.40  Index Matching       : 0.00
% 2.76/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
