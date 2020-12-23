%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 207 expanded)
%              Number of leaves         :   42 (  91 expanded)
%              Depth                    :    9
%              Number of atoms          :  176 ( 526 expanded)
%              Number of equality atoms :   59 ( 146 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_111,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_103,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => k9_relat_1(B,k10_relat_1(B,A)) = k3_xboole_0(A,k9_relat_1(B,k1_relat_1(B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

tff(c_44,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_426,plain,(
    ! [C_110,A_111,B_112] :
      ( v1_relat_1(C_110)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(k2_zfmisc_1(A_111,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_430,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_426])).

tff(c_52,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_586,plain,(
    ! [C_154,A_155,B_156] :
      ( v2_funct_1(C_154)
      | ~ v3_funct_2(C_154,A_155,B_156)
      | ~ v1_funct_1(C_154)
      | ~ m1_subset_1(C_154,k1_zfmisc_1(k2_zfmisc_1(A_155,B_156))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_589,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_586])).

tff(c_592,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_589])).

tff(c_50,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_553,plain,(
    ! [A_146,B_147,C_148] :
      ( k1_relset_1(A_146,B_147,C_148) = k1_relat_1(C_148)
      | ~ m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_146,B_147))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_557,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_553])).

tff(c_686,plain,(
    ! [A_171,B_172] :
      ( k1_relset_1(A_171,A_171,B_172) = A_171
      | ~ m1_subset_1(B_172,k1_zfmisc_1(k2_zfmisc_1(A_171,A_171)))
      | ~ v1_funct_2(B_172,A_171,A_171)
      | ~ v1_funct_1(B_172) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_689,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_686])).

tff(c_692,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_557,c_689])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( k10_relat_1(B_12,k9_relat_1(B_12,A_11)) = A_11
      | ~ v2_funct_1(B_12)
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_funct_1(B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_702,plain,(
    ! [A_11] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_11)) = A_11
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_11,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_692,c_16])).

tff(c_782,plain,(
    ! [A_176] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_176)) = A_176
      | ~ r1_tarski(A_176,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_52,c_592,c_702])).

tff(c_594,plain,(
    ! [A_157,B_158,C_159,D_160] :
      ( k8_relset_1(A_157,B_158,C_159,D_160) = k10_relat_1(C_159,D_160)
      | ~ m1_subset_1(C_159,k1_zfmisc_1(k2_zfmisc_1(A_157,B_158))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_597,plain,(
    ! [D_160] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_160) = k10_relat_1('#skF_3',D_160) ),
    inference(resolution,[status(thm)],[c_46,c_594])).

tff(c_562,plain,(
    ! [A_149,B_150,C_151,D_152] :
      ( k7_relset_1(A_149,B_150,C_151,D_152) = k9_relat_1(C_151,D_152)
      | ~ m1_subset_1(C_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_565,plain,(
    ! [D_152] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_152) = k9_relat_1('#skF_3',D_152) ),
    inference(resolution,[status(thm)],[c_46,c_562])).

tff(c_55,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = A_38
      | ~ r1_tarski(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_55])).

tff(c_89,plain,(
    ! [C_43,A_44,B_45] :
      ( v1_relat_1(C_43)
      | ~ m1_subset_1(C_43,k1_zfmisc_1(k2_zfmisc_1(A_44,B_45))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_89])).

tff(c_94,plain,(
    ! [C_46,B_47,A_48] :
      ( v5_relat_1(C_46,B_47)
      | ~ m1_subset_1(C_46,k1_zfmisc_1(k2_zfmisc_1(A_48,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_46,c_94])).

tff(c_144,plain,(
    ! [B_59,A_60] :
      ( k2_relat_1(B_59) = A_60
      | ~ v2_funct_2(B_59,A_60)
      | ~ v5_relat_1(B_59,A_60)
      | ~ v1_relat_1(B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_147,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_98,c_144])).

tff(c_150,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_147])).

tff(c_151,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_150])).

tff(c_196,plain,(
    ! [C_77,B_78,A_79] :
      ( v2_funct_2(C_77,B_78)
      | ~ v3_funct_2(C_77,A_79,B_78)
      | ~ v1_funct_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_79,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_199,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_196])).

tff(c_202,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_48,c_199])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_151,c_202])).

tff(c_205,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_150])).

tff(c_217,plain,(
    ! [A_80,B_81,C_82] :
      ( k1_relset_1(A_80,B_81,C_82) = k1_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_221,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_217])).

tff(c_293,plain,(
    ! [A_103,B_104] :
      ( k1_relset_1(A_103,A_103,B_104) = A_103
      | ~ m1_subset_1(B_104,k1_zfmisc_1(k2_zfmisc_1(A_103,A_103)))
      | ~ v1_funct_2(B_104,A_103,A_103)
      | ~ v1_funct_1(B_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_296,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_293])).

tff(c_299,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_221,c_296])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_54,A_55] :
      ( k7_relat_1(B_54,A_55) = B_54
      | ~ r1_tarski(k1_relat_1(B_54),A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_119,plain,(
    ! [B_56] :
      ( k7_relat_1(B_56,k1_relat_1(B_56)) = B_56
      | ~ v1_relat_1(B_56) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_10,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_125,plain,(
    ! [B_56] :
      ( k9_relat_1(B_56,k1_relat_1(B_56)) = k2_relat_1(B_56)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(B_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_309,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_125])).

tff(c_323,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_93,c_205,c_309])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,k9_relat_1(B_10,k1_relat_1(B_10))) = k9_relat_1(B_10,k10_relat_1(B_10,A_9))
      | ~ v1_funct_1(B_10)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_306,plain,(
    ! [A_9] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_9)) = k3_xboole_0(A_9,k9_relat_1('#skF_3','#skF_1'))
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_299,c_14])).

tff(c_321,plain,(
    ! [A_9] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_9)) = k3_xboole_0(A_9,k9_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_52,c_306])).

tff(c_408,plain,(
    ! [A_9] : k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_9)) = k3_xboole_0(A_9,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_321])).

tff(c_247,plain,(
    ! [A_91,B_92,C_93,D_94] :
      ( k7_relset_1(A_91,B_92,C_93,D_94) = k9_relat_1(C_93,D_94)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_250,plain,(
    ! [D_94] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_94) = k9_relat_1('#skF_3',D_94) ),
    inference(resolution,[status(thm)],[c_46,c_247])).

tff(c_233,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( k8_relset_1(A_86,B_87,C_88,D_89) = k10_relat_1(C_88,D_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_236,plain,(
    ! [D_89] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_89) = k10_relat_1('#skF_3',D_89) ),
    inference(resolution,[status(thm)],[c_46,c_233])).

tff(c_42,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_77,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_237,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_77])).

tff(c_251,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_237])).

tff(c_409,plain,(
    k3_xboole_0('#skF_2','#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_408,c_251])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_409])).

tff(c_413,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_566,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_413])).

tff(c_599,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_566])).

tff(c_796,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_599])).

tff(c_826,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_796])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.44  
% 2.65/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.44  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.44  
% 2.65/1.44  %Foreground sorts:
% 2.65/1.44  
% 2.65/1.44  
% 2.65/1.44  %Background operators:
% 2.65/1.44  
% 2.65/1.44  
% 2.65/1.44  %Foreground operators:
% 2.65/1.44  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.44  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.44  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.44  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.65/1.44  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.44  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 2.65/1.44  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.44  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.65/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.44  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.44  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.65/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.44  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 2.65/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.44  
% 2.65/1.46  tff(f_126, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 2.65/1.46  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.65/1.46  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 2.65/1.46  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.65/1.46  tff(f_111, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 2.65/1.46  tff(f_61, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 2.65/1.46  tff(f_83, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 2.65/1.46  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.65/1.46  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.65/1.46  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.65/1.46  tff(f_103, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 2.65/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.65/1.46  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.65/1.46  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.65/1.46  tff(f_51, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = k3_xboole_0(A, k9_relat_1(B, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_funct_1)).
% 2.65/1.46  tff(c_44, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_426, plain, (![C_110, A_111, B_112]: (v1_relat_1(C_110) | ~m1_subset_1(C_110, k1_zfmisc_1(k2_zfmisc_1(A_111, B_112))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.46  tff(c_430, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_426])).
% 2.65/1.46  tff(c_52, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_48, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_586, plain, (![C_154, A_155, B_156]: (v2_funct_1(C_154) | ~v3_funct_2(C_154, A_155, B_156) | ~v1_funct_1(C_154) | ~m1_subset_1(C_154, k1_zfmisc_1(k2_zfmisc_1(A_155, B_156))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.65/1.46  tff(c_589, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_586])).
% 2.65/1.46  tff(c_592, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_589])).
% 2.65/1.46  tff(c_50, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_553, plain, (![A_146, B_147, C_148]: (k1_relset_1(A_146, B_147, C_148)=k1_relat_1(C_148) | ~m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_146, B_147))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.46  tff(c_557, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_553])).
% 2.65/1.46  tff(c_686, plain, (![A_171, B_172]: (k1_relset_1(A_171, A_171, B_172)=A_171 | ~m1_subset_1(B_172, k1_zfmisc_1(k2_zfmisc_1(A_171, A_171))) | ~v1_funct_2(B_172, A_171, A_171) | ~v1_funct_1(B_172))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.65/1.46  tff(c_689, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_686])).
% 2.65/1.46  tff(c_692, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_557, c_689])).
% 2.65/1.46  tff(c_16, plain, (![B_12, A_11]: (k10_relat_1(B_12, k9_relat_1(B_12, A_11))=A_11 | ~v2_funct_1(B_12) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_funct_1(B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.46  tff(c_702, plain, (![A_11]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_11))=A_11 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_11, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_692, c_16])).
% 2.65/1.46  tff(c_782, plain, (![A_176]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_176))=A_176 | ~r1_tarski(A_176, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_430, c_52, c_592, c_702])).
% 2.65/1.46  tff(c_594, plain, (![A_157, B_158, C_159, D_160]: (k8_relset_1(A_157, B_158, C_159, D_160)=k10_relat_1(C_159, D_160) | ~m1_subset_1(C_159, k1_zfmisc_1(k2_zfmisc_1(A_157, B_158))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.46  tff(c_597, plain, (![D_160]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_160)=k10_relat_1('#skF_3', D_160))), inference(resolution, [status(thm)], [c_46, c_594])).
% 2.65/1.46  tff(c_562, plain, (![A_149, B_150, C_151, D_152]: (k7_relset_1(A_149, B_150, C_151, D_152)=k9_relat_1(C_151, D_152) | ~m1_subset_1(C_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.46  tff(c_565, plain, (![D_152]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_152)=k9_relat_1('#skF_3', D_152))), inference(resolution, [status(thm)], [c_46, c_562])).
% 2.65/1.46  tff(c_55, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=A_38 | ~r1_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.65/1.46  tff(c_63, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_44, c_55])).
% 2.65/1.46  tff(c_89, plain, (![C_43, A_44, B_45]: (v1_relat_1(C_43) | ~m1_subset_1(C_43, k1_zfmisc_1(k2_zfmisc_1(A_44, B_45))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.65/1.46  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_89])).
% 2.65/1.46  tff(c_94, plain, (![C_46, B_47, A_48]: (v5_relat_1(C_46, B_47) | ~m1_subset_1(C_46, k1_zfmisc_1(k2_zfmisc_1(A_48, B_47))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.65/1.46  tff(c_98, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_46, c_94])).
% 2.65/1.46  tff(c_144, plain, (![B_59, A_60]: (k2_relat_1(B_59)=A_60 | ~v2_funct_2(B_59, A_60) | ~v5_relat_1(B_59, A_60) | ~v1_relat_1(B_59))), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.65/1.46  tff(c_147, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_98, c_144])).
% 2.65/1.46  tff(c_150, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_147])).
% 2.65/1.46  tff(c_151, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_150])).
% 2.65/1.46  tff(c_196, plain, (![C_77, B_78, A_79]: (v2_funct_2(C_77, B_78) | ~v3_funct_2(C_77, A_79, B_78) | ~v1_funct_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_79, B_78))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.65/1.46  tff(c_199, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_196])).
% 2.65/1.46  tff(c_202, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_48, c_199])).
% 2.65/1.46  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_151, c_202])).
% 2.65/1.46  tff(c_205, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_150])).
% 2.65/1.46  tff(c_217, plain, (![A_80, B_81, C_82]: (k1_relset_1(A_80, B_81, C_82)=k1_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.65/1.46  tff(c_221, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_217])).
% 2.65/1.46  tff(c_293, plain, (![A_103, B_104]: (k1_relset_1(A_103, A_103, B_104)=A_103 | ~m1_subset_1(B_104, k1_zfmisc_1(k2_zfmisc_1(A_103, A_103))) | ~v1_funct_2(B_104, A_103, A_103) | ~v1_funct_1(B_104))), inference(cnfTransformation, [status(thm)], [f_111])).
% 2.65/1.46  tff(c_296, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_293])).
% 2.65/1.46  tff(c_299, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_221, c_296])).
% 2.65/1.46  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.65/1.46  tff(c_113, plain, (![B_54, A_55]: (k7_relat_1(B_54, A_55)=B_54 | ~r1_tarski(k1_relat_1(B_54), A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.65/1.46  tff(c_119, plain, (![B_56]: (k7_relat_1(B_56, k1_relat_1(B_56))=B_56 | ~v1_relat_1(B_56))), inference(resolution, [status(thm)], [c_6, c_113])).
% 2.65/1.46  tff(c_10, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.65/1.46  tff(c_125, plain, (![B_56]: (k9_relat_1(B_56, k1_relat_1(B_56))=k2_relat_1(B_56) | ~v1_relat_1(B_56) | ~v1_relat_1(B_56))), inference(superposition, [status(thm), theory('equality')], [c_119, c_10])).
% 2.65/1.46  tff(c_309, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_299, c_125])).
% 2.65/1.46  tff(c_323, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_93, c_205, c_309])).
% 2.65/1.46  tff(c_14, plain, (![A_9, B_10]: (k3_xboole_0(A_9, k9_relat_1(B_10, k1_relat_1(B_10)))=k9_relat_1(B_10, k10_relat_1(B_10, A_9)) | ~v1_funct_1(B_10) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.65/1.46  tff(c_306, plain, (![A_9]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_9))=k3_xboole_0(A_9, k9_relat_1('#skF_3', '#skF_1')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_299, c_14])).
% 2.65/1.46  tff(c_321, plain, (![A_9]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_9))=k3_xboole_0(A_9, k9_relat_1('#skF_3', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_52, c_306])).
% 2.65/1.46  tff(c_408, plain, (![A_9]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_9))=k3_xboole_0(A_9, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_321])).
% 2.65/1.46  tff(c_247, plain, (![A_91, B_92, C_93, D_94]: (k7_relset_1(A_91, B_92, C_93, D_94)=k9_relat_1(C_93, D_94) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.65/1.46  tff(c_250, plain, (![D_94]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_94)=k9_relat_1('#skF_3', D_94))), inference(resolution, [status(thm)], [c_46, c_247])).
% 2.65/1.46  tff(c_233, plain, (![A_86, B_87, C_88, D_89]: (k8_relset_1(A_86, B_87, C_88, D_89)=k10_relat_1(C_88, D_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.65/1.46  tff(c_236, plain, (![D_89]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_89)=k10_relat_1('#skF_3', D_89))), inference(resolution, [status(thm)], [c_46, c_233])).
% 2.65/1.46  tff(c_42, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 2.65/1.46  tff(c_77, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_42])).
% 2.65/1.46  tff(c_237, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_236, c_77])).
% 2.65/1.46  tff(c_251, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_237])).
% 2.65/1.46  tff(c_409, plain, (k3_xboole_0('#skF_2', '#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_408, c_251])).
% 2.65/1.46  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_409])).
% 2.65/1.46  tff(c_413, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_42])).
% 2.65/1.46  tff(c_566, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_565, c_413])).
% 2.65/1.46  tff(c_599, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_597, c_566])).
% 2.65/1.46  tff(c_796, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_782, c_599])).
% 2.65/1.46  tff(c_826, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_796])).
% 2.65/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.46  
% 2.65/1.46  Inference rules
% 2.65/1.46  ----------------------
% 2.65/1.46  #Ref     : 0
% 2.65/1.46  #Sup     : 180
% 2.65/1.46  #Fact    : 0
% 2.65/1.46  #Define  : 0
% 2.65/1.46  #Split   : 5
% 2.65/1.46  #Chain   : 0
% 2.65/1.46  #Close   : 0
% 2.65/1.46  
% 2.65/1.46  Ordering : KBO
% 2.65/1.46  
% 2.65/1.46  Simplification rules
% 2.65/1.46  ----------------------
% 2.65/1.46  #Subsume      : 1
% 2.65/1.46  #Demod        : 151
% 2.65/1.46  #Tautology    : 109
% 2.65/1.46  #SimpNegUnit  : 2
% 2.65/1.46  #BackRed      : 13
% 2.65/1.46  
% 2.65/1.46  #Partial instantiations: 0
% 2.65/1.46  #Strategies tried      : 1
% 2.65/1.46  
% 2.65/1.46  Timing (in seconds)
% 2.65/1.46  ----------------------
% 3.06/1.47  Preprocessing        : 0.32
% 3.06/1.47  Parsing              : 0.17
% 3.06/1.47  CNF conversion       : 0.02
% 3.06/1.47  Main loop            : 0.33
% 3.06/1.47  Inferencing          : 0.13
% 3.06/1.47  Reduction            : 0.10
% 3.06/1.47  Demodulation         : 0.07
% 3.06/1.47  BG Simplification    : 0.02
% 3.06/1.47  Subsumption          : 0.04
% 3.06/1.47  Abstraction          : 0.02
% 3.06/1.47  MUC search           : 0.00
% 3.06/1.47  Cooper               : 0.00
% 3.06/1.47  Total                : 0.69
% 3.06/1.47  Index Insertion      : 0.00
% 3.06/1.47  Index Deletion       : 0.00
% 3.06/1.47  Index Matching       : 0.00
% 3.06/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
