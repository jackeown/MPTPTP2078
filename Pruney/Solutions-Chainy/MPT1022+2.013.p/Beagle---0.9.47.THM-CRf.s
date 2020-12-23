%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 4.66s
% Output     : CNFRefutation 4.78s
% Verified   : 
% Statistics : Number of formulae       :  210 (2225 expanded)
%              Number of leaves         :   44 ( 793 expanded)
%              Depth                    :   20
%              Number of atoms          :  448 (6498 expanded)
%              Number of equality atoms :  101 (1261 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

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

tff(f_160,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_145,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_135,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_119,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_56,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_58,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_68,plain,(
    ! [B_44,A_45] :
      ( v1_relat_1(B_44)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_45))
      | ~ v1_relat_1(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_71,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_58,c_68])).

tff(c_74,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_71])).

tff(c_64,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_60,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_755,plain,(
    ! [C_164,A_165,B_166] :
      ( v2_funct_1(C_164)
      | ~ v3_funct_2(C_164,A_165,B_166)
      | ~ v1_funct_1(C_164)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_758,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_755])).

tff(c_761,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_758])).

tff(c_453,plain,(
    ! [C_120,A_121,B_122] :
      ( v4_relat_1(C_120,A_121)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_457,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_453])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_1116,plain,(
    ! [A_188,B_189] :
      ( k2_funct_2(A_188,B_189) = k2_funct_1(B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1119,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1116])).

tff(c_1122,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1119])).

tff(c_942,plain,(
    ! [A_182,B_183] :
      ( v1_funct_1(k2_funct_2(A_182,B_183))
      | ~ m1_subset_1(B_183,k1_zfmisc_1(k2_zfmisc_1(A_182,A_182)))
      | ~ v3_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_2(B_183,A_182,A_182)
      | ~ v1_funct_1(B_183) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_945,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_942])).

tff(c_948,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_945])).

tff(c_1123,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1122,c_948])).

tff(c_418,plain,(
    ! [B_114,A_115] :
      ( v4_relat_1(B_114,A_115)
      | ~ r1_tarski(k1_relat_1(B_114),A_115)
      | ~ v1_relat_1(B_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_423,plain,(
    ! [B_114] :
      ( v4_relat_1(B_114,k1_relat_1(B_114))
      | ~ v1_relat_1(B_114) ) ),
    inference(resolution,[status(thm)],[c_6,c_418])).

tff(c_403,plain,(
    ! [C_107,B_108,A_109] :
      ( v5_relat_1(C_107,B_108)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(k2_zfmisc_1(A_109,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_407,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_403])).

tff(c_490,plain,(
    ! [B_125,A_126] :
      ( k2_relat_1(B_125) = A_126
      | ~ v2_funct_2(B_125,A_126)
      | ~ v5_relat_1(B_125,A_126)
      | ~ v1_relat_1(B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_493,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_407,c_490])).

tff(c_496,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_493])).

tff(c_497,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_584,plain,(
    ! [C_145,B_146,A_147] :
      ( v2_funct_2(C_145,B_146)
      | ~ v3_funct_2(C_145,A_147,B_146)
      | ~ v1_funct_1(C_145)
      | ~ m1_subset_1(C_145,k1_zfmisc_1(k2_zfmisc_1(A_147,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_587,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_584])).

tff(c_590,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_587])).

tff(c_592,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_497,c_590])).

tff(c_593,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_424,plain,(
    ! [B_116] :
      ( v4_relat_1(B_116,k1_relat_1(B_116))
      | ~ v1_relat_1(B_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_418])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k7_relat_1(B_13,A_12) = B_13
      | ~ v4_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_429,plain,(
    ! [B_117] :
      ( k7_relat_1(B_117,k1_relat_1(B_117)) = B_117
      | ~ v1_relat_1(B_117) ) ),
    inference(resolution,[status(thm)],[c_424,c_18])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_435,plain,(
    ! [B_117] :
      ( k9_relat_1(B_117,k1_relat_1(B_117)) = k2_relat_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_16])).

tff(c_797,plain,(
    ! [A_173,B_174] :
      ( k9_relat_1(k2_funct_1(A_173),k9_relat_1(A_173,B_174)) = B_174
      | ~ r1_tarski(B_174,k1_relat_1(A_173))
      | ~ v2_funct_1(A_173)
      | ~ v1_funct_1(A_173)
      | ~ v1_relat_1(A_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_827,plain,(
    ! [B_117] :
      ( k9_relat_1(k2_funct_1(B_117),k2_relat_1(B_117)) = k1_relat_1(B_117)
      | ~ r1_tarski(k1_relat_1(B_117),k1_relat_1(B_117))
      | ~ v2_funct_1(B_117)
      | ~ v1_funct_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_797])).

tff(c_850,plain,(
    ! [B_177] :
      ( k9_relat_1(k2_funct_1(B_177),k2_relat_1(B_177)) = k1_relat_1(B_177)
      | ~ v2_funct_1(B_177)
      | ~ v1_funct_1(B_177)
      | ~ v1_relat_1(B_177) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_827])).

tff(c_862,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_850])).

tff(c_869,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_862])).

tff(c_769,plain,(
    ! [B_170,A_171] :
      ( k10_relat_1(B_170,k9_relat_1(B_170,A_171)) = A_171
      | ~ v2_funct_1(B_170)
      | ~ r1_tarski(A_171,k1_relat_1(B_170))
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_778,plain,(
    ! [B_172] :
      ( k10_relat_1(B_172,k9_relat_1(B_172,k1_relat_1(B_172))) = k1_relat_1(B_172)
      | ~ v2_funct_1(B_172)
      | ~ v1_funct_1(B_172)
      | ~ v1_relat_1(B_172) ) ),
    inference(resolution,[status(thm)],[c_6,c_769])).

tff(c_889,plain,(
    ! [B_181] :
      ( k10_relat_1(B_181,k2_relat_1(B_181)) = k1_relat_1(B_181)
      | ~ v2_funct_1(B_181)
      | ~ v1_funct_1(B_181)
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(B_181)
      | ~ v1_relat_1(B_181) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_435,c_778])).

tff(c_20,plain,(
    ! [B_15,A_14] :
      ( k9_relat_1(B_15,k10_relat_1(B_15,A_14)) = A_14
      | ~ r1_tarski(A_14,k2_relat_1(B_15))
      | ~ v1_funct_1(B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_609,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_20])).

tff(c_616,plain,(
    ! [A_14] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_14)) = A_14
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_609])).

tff(c_821,plain,(
    ! [A_14] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_14) = k10_relat_1('#skF_3',A_14)
      | ~ r1_tarski(k10_relat_1('#skF_3',A_14),k1_relat_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3')
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_797])).

tff(c_835,plain,(
    ! [A_14] :
      ( k9_relat_1(k2_funct_1('#skF_3'),A_14) = k10_relat_1('#skF_3',A_14)
      | ~ r1_tarski(k10_relat_1('#skF_3',A_14),k1_relat_1('#skF_3'))
      | ~ r1_tarski(A_14,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_821])).

tff(c_896,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = k10_relat_1('#skF_3',k2_relat_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_889,c_835])).

tff(c_915,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_74,c_74,c_64,c_761,c_6,c_593,c_6,c_869,c_593,c_593,c_896])).

tff(c_595,plain,(
    ! [B_148,A_149] :
      ( k9_relat_1(B_148,k10_relat_1(B_148,A_149)) = A_149
      | ~ r1_tarski(A_149,k2_relat_1(B_148))
      | ~ v1_funct_1(B_148)
      | ~ v1_relat_1(B_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_646,plain,(
    ! [B_153] :
      ( k9_relat_1(B_153,k10_relat_1(B_153,k2_relat_1(B_153))) = k2_relat_1(B_153)
      | ~ v1_funct_1(B_153)
      | ~ v1_relat_1(B_153) ) ),
    inference(resolution,[status(thm)],[c_6,c_595])).

tff(c_663,plain,
    ( k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = k2_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_646])).

tff(c_674,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_593,c_663])).

tff(c_815,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k10_relat_1('#skF_3','#skF_1')
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_674,c_797])).

tff(c_833,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k10_relat_1('#skF_3','#skF_1')
    | ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_815])).

tff(c_842,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_833])).

tff(c_921,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_915,c_842])).

tff(c_925,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_921])).

tff(c_926,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k10_relat_1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_977,plain,(
    ! [B_185] :
      ( k9_relat_1(k2_funct_1(B_185),k2_relat_1(B_185)) = k1_relat_1(B_185)
      | ~ v2_funct_1(B_185)
      | ~ v1_funct_1(B_185)
      | ~ v1_relat_1(B_185) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_827])).

tff(c_989,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_593,c_977])).

tff(c_996,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_926,c_989])).

tff(c_927,plain,(
    r1_tarski(k10_relat_1('#skF_3','#skF_1'),k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_833])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_941,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_927,c_2])).

tff(c_970,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_941])).

tff(c_997,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_996,c_970])).

tff(c_1004,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_997])).

tff(c_1005,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_941])).

tff(c_441,plain,(
    ! [B_118,A_119] :
      ( r1_tarski(k1_relat_1(B_118),A_119)
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_448,plain,(
    ! [B_118,A_119] :
      ( k1_relat_1(B_118) = A_119
      | ~ r1_tarski(A_119,k1_relat_1(B_118))
      | ~ v4_relat_1(B_118,A_119)
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_441,c_2])).

tff(c_932,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_927,c_448])).

tff(c_940,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v4_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_932])).

tff(c_956,plain,(
    ~ v4_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_940])).

tff(c_1019,plain,(
    ~ v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1005,c_956])).

tff(c_1064,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_1019])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1064])).

tff(c_1069,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_940])).

tff(c_24,plain,(
    ! [A_18,B_20] :
      ( k9_relat_1(k2_funct_1(A_18),k9_relat_1(A_18,B_20)) = B_20
      | ~ r1_tarski(B_20,k1_relat_1(A_18))
      | ~ v2_funct_1(A_18)
      | ~ v1_funct_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_952,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k10_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_24])).

tff(c_1213,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1069,c_952])).

tff(c_1214,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1213])).

tff(c_1402,plain,(
    ! [A_207,B_208] :
      ( m1_subset_1(k2_funct_2(A_207,B_208),k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ m1_subset_1(B_208,k1_zfmisc_1(k2_zfmisc_1(A_207,A_207)))
      | ~ v3_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_2(B_208,A_207,A_207)
      | ~ v1_funct_1(B_208) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1434,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_1402])).

tff(c_1449,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_1434])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1478,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1449,c_8])).

tff(c_1503,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1478])).

tff(c_1505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1214,c_1503])).

tff(c_1507,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_1175,plain,(
    ! [A_191,B_192] :
      ( v3_funct_2(k2_funct_2(A_191,B_192),A_191,A_191)
      | ~ m1_subset_1(B_192,k1_zfmisc_1(k2_zfmisc_1(A_191,A_191)))
      | ~ v3_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_2(B_192,A_191,A_191)
      | ~ v1_funct_1(B_192) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1177,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1175])).

tff(c_1180,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_1122,c_1177])).

tff(c_2328,plain,(
    ! [A_236,B_237] :
      ( m1_subset_1(k2_funct_2(A_236,B_237),k1_zfmisc_1(k2_zfmisc_1(A_236,A_236)))
      | ~ m1_subset_1(B_237,k1_zfmisc_1(k2_zfmisc_1(A_236,A_236)))
      | ~ v3_funct_2(B_237,A_236,A_236)
      | ~ v1_funct_2(B_237,A_236,A_236)
      | ~ v1_funct_1(B_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_2360,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1122,c_2328])).

tff(c_2375,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_62,c_60,c_58,c_2360])).

tff(c_34,plain,(
    ! [C_34,B_33,A_32] :
      ( v2_funct_2(C_34,B_33)
      | ~ v3_funct_2(C_34,A_32,B_33)
      | ~ v1_funct_1(C_34)
      | ~ m1_subset_1(C_34,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_2388,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2375,c_34])).

tff(c_2419,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1180,c_2388])).

tff(c_26,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2426,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2375,c_26])).

tff(c_42,plain,(
    ! [B_36,A_35] :
      ( k2_relat_1(B_36) = A_35
      | ~ v2_funct_2(B_36,A_35)
      | ~ v5_relat_1(B_36,A_35)
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2438,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2426,c_42])).

tff(c_2441,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_2419,c_2438])).

tff(c_1071,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1069,c_926])).

tff(c_28,plain,(
    ! [C_23,A_21,B_22] :
      ( v4_relat_1(C_23,A_21)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2425,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2375,c_28])).

tff(c_2432,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2425,c_18])).

tff(c_2435,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_2432])).

tff(c_2490,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2435,c_16])).

tff(c_2500,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1507,c_2441,c_1071,c_2490])).

tff(c_460,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_457,c_18])).

tff(c_463,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_460])).

tff(c_467,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_16])).

tff(c_471,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_467])).

tff(c_606,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_593,c_471])).

tff(c_824,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_797])).

tff(c_837,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_824])).

tff(c_840,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_837])).

tff(c_2509,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2500,c_840])).

tff(c_2515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2509])).

tff(c_2517,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_837])).

tff(c_2529,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2517,c_448])).

tff(c_2537,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_457,c_2529])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( k10_relat_1(B_17,k9_relat_1(B_17,A_16)) = A_16
      | ~ v2_funct_1(B_17)
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2546,plain,(
    ! [A_16] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_16)) = A_16
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2537,c_22])).

tff(c_2671,plain,(
    ! [A_246] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_246)) = A_246
      | ~ r1_tarski(A_246,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_761,c_2546])).

tff(c_695,plain,(
    ! [A_158,B_159,C_160,D_161] :
      ( k8_relset_1(A_158,B_159,C_160,D_161) = k10_relat_1(C_160,D_161)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_698,plain,(
    ! [D_161] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_161) = k10_relat_1('#skF_3',D_161) ),
    inference(resolution,[status(thm)],[c_58,c_695])).

tff(c_691,plain,(
    ! [A_154,B_155,C_156,D_157] :
      ( k7_relset_1(A_154,B_155,C_156,D_157) = k9_relat_1(C_156,D_157)
      | ~ m1_subset_1(C_156,k1_zfmisc_1(k2_zfmisc_1(A_154,B_155))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_694,plain,(
    ! [D_157] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_157) = k9_relat_1('#skF_3',D_157) ),
    inference(resolution,[status(thm)],[c_58,c_691])).

tff(c_88,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_92,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_88])).

tff(c_170,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(B_66) = A_67
      | ~ v2_funct_2(B_66,A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_173,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_170])).

tff(c_176,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_173])).

tff(c_177,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_248,plain,(
    ! [C_86,B_87,A_88] :
      ( v2_funct_2(C_86,B_87)
      | ~ v3_funct_2(C_86,A_88,B_87)
      | ~ v1_funct_1(C_86)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_251,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_248])).

tff(c_254,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_251])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_254])).

tff(c_257,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_300,plain,(
    ! [B_96,A_97] :
      ( k9_relat_1(B_96,k10_relat_1(B_96,A_97)) = A_97
      | ~ r1_tarski(A_97,k2_relat_1(B_96))
      | ~ v1_funct_1(B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_302,plain,(
    ! [A_97] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_97)) = A_97
      | ~ r1_tarski(A_97,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_300])).

tff(c_312,plain,(
    ! [A_97] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_97)) = A_97
      | ~ r1_tarski(A_97,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_64,c_302])).

tff(c_369,plain,(
    ! [A_100,B_101,C_102,D_103] :
      ( k8_relset_1(A_100,B_101,C_102,D_103) = k10_relat_1(C_102,D_103)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_372,plain,(
    ! [D_103] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_103) = k10_relat_1('#skF_3',D_103) ),
    inference(resolution,[status(thm)],[c_58,c_369])).

tff(c_269,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_relset_1(A_89,B_90,C_91,D_92) = k9_relat_1(C_91,D_92)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_272,plain,(
    ! [D_92] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_92) = k9_relat_1('#skF_3',D_92) ),
    inference(resolution,[status(thm)],[c_58,c_269])).

tff(c_54,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_75,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_278,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_75])).

tff(c_373,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_278])).

tff(c_385,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_312,c_373])).

tff(c_389,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_385])).

tff(c_390,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_699,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_694,c_390])).

tff(c_725,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_698,c_699])).

tff(c_2681,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2671,c_725])).

tff(c_2715,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_2681])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:47:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.66/1.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.83  
% 4.78/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.84  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.78/1.84  
% 4.78/1.84  %Foreground sorts:
% 4.78/1.84  
% 4.78/1.84  
% 4.78/1.84  %Background operators:
% 4.78/1.84  
% 4.78/1.84  
% 4.78/1.84  %Foreground operators:
% 4.78/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.78/1.84  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.78/1.84  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.78/1.84  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.78/1.84  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.78/1.84  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.78/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.78/1.84  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.78/1.84  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.78/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.78/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.78/1.84  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.78/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.78/1.84  tff('#skF_1', type, '#skF_1': $i).
% 4.78/1.84  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.78/1.84  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.78/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.78/1.84  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.78/1.84  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.78/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.78/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.78/1.84  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.78/1.84  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.78/1.84  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.78/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.78/1.84  
% 4.78/1.87  tff(f_160, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 4.78/1.87  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.78/1.87  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.78/1.87  tff(f_111, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.78/1.87  tff(f_91, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.78/1.87  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.78/1.87  tff(f_145, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.78/1.87  tff(f_135, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.78/1.87  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 4.78/1.87  tff(f_119, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 4.78/1.87  tff(f_56, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.78/1.87  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.78/1.87  tff(f_85, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t177_funct_1)).
% 4.78/1.87  tff(f_74, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.78/1.87  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 4.78/1.87  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.78/1.87  tff(f_95, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.78/1.87  tff(c_56, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.78/1.87  tff(c_58, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_68, plain, (![B_44, A_45]: (v1_relat_1(B_44) | ~m1_subset_1(B_44, k1_zfmisc_1(A_45)) | ~v1_relat_1(A_45))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.78/1.87  tff(c_71, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_68])).
% 4.78/1.87  tff(c_74, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_71])).
% 4.78/1.87  tff(c_64, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_60, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_755, plain, (![C_164, A_165, B_166]: (v2_funct_1(C_164) | ~v3_funct_2(C_164, A_165, B_166) | ~v1_funct_1(C_164) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.78/1.87  tff(c_758, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_755])).
% 4.78/1.87  tff(c_761, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_758])).
% 4.78/1.87  tff(c_453, plain, (![C_120, A_121, B_122]: (v4_relat_1(C_120, A_121) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.87  tff(c_457, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_453])).
% 4.78/1.87  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.78/1.87  tff(c_62, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_1116, plain, (![A_188, B_189]: (k2_funct_2(A_188, B_189)=k2_funct_1(B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_189, A_188, A_188) | ~v1_funct_2(B_189, A_188, A_188) | ~v1_funct_1(B_189))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.78/1.87  tff(c_1119, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1116])).
% 4.78/1.87  tff(c_1122, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1119])).
% 4.78/1.87  tff(c_942, plain, (![A_182, B_183]: (v1_funct_1(k2_funct_2(A_182, B_183)) | ~m1_subset_1(B_183, k1_zfmisc_1(k2_zfmisc_1(A_182, A_182))) | ~v3_funct_2(B_183, A_182, A_182) | ~v1_funct_2(B_183, A_182, A_182) | ~v1_funct_1(B_183))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.87  tff(c_945, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_942])).
% 4.78/1.87  tff(c_948, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_945])).
% 4.78/1.87  tff(c_1123, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1122, c_948])).
% 4.78/1.87  tff(c_418, plain, (![B_114, A_115]: (v4_relat_1(B_114, A_115) | ~r1_tarski(k1_relat_1(B_114), A_115) | ~v1_relat_1(B_114))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.78/1.87  tff(c_423, plain, (![B_114]: (v4_relat_1(B_114, k1_relat_1(B_114)) | ~v1_relat_1(B_114))), inference(resolution, [status(thm)], [c_6, c_418])).
% 4.78/1.87  tff(c_403, plain, (![C_107, B_108, A_109]: (v5_relat_1(C_107, B_108) | ~m1_subset_1(C_107, k1_zfmisc_1(k2_zfmisc_1(A_109, B_108))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.87  tff(c_407, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_403])).
% 4.78/1.87  tff(c_490, plain, (![B_125, A_126]: (k2_relat_1(B_125)=A_126 | ~v2_funct_2(B_125, A_126) | ~v5_relat_1(B_125, A_126) | ~v1_relat_1(B_125))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.78/1.87  tff(c_493, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_407, c_490])).
% 4.78/1.87  tff(c_496, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_493])).
% 4.78/1.87  tff(c_497, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_496])).
% 4.78/1.87  tff(c_584, plain, (![C_145, B_146, A_147]: (v2_funct_2(C_145, B_146) | ~v3_funct_2(C_145, A_147, B_146) | ~v1_funct_1(C_145) | ~m1_subset_1(C_145, k1_zfmisc_1(k2_zfmisc_1(A_147, B_146))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.78/1.87  tff(c_587, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_584])).
% 4.78/1.87  tff(c_590, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_587])).
% 4.78/1.87  tff(c_592, plain, $false, inference(negUnitSimplification, [status(thm)], [c_497, c_590])).
% 4.78/1.87  tff(c_593, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_496])).
% 4.78/1.87  tff(c_424, plain, (![B_116]: (v4_relat_1(B_116, k1_relat_1(B_116)) | ~v1_relat_1(B_116))), inference(resolution, [status(thm)], [c_6, c_418])).
% 4.78/1.87  tff(c_18, plain, (![B_13, A_12]: (k7_relat_1(B_13, A_12)=B_13 | ~v4_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.78/1.87  tff(c_429, plain, (![B_117]: (k7_relat_1(B_117, k1_relat_1(B_117))=B_117 | ~v1_relat_1(B_117))), inference(resolution, [status(thm)], [c_424, c_18])).
% 4.78/1.87  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.78/1.87  tff(c_435, plain, (![B_117]: (k9_relat_1(B_117, k1_relat_1(B_117))=k2_relat_1(B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_429, c_16])).
% 4.78/1.87  tff(c_797, plain, (![A_173, B_174]: (k9_relat_1(k2_funct_1(A_173), k9_relat_1(A_173, B_174))=B_174 | ~r1_tarski(B_174, k1_relat_1(A_173)) | ~v2_funct_1(A_173) | ~v1_funct_1(A_173) | ~v1_relat_1(A_173))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.78/1.87  tff(c_827, plain, (![B_117]: (k9_relat_1(k2_funct_1(B_117), k2_relat_1(B_117))=k1_relat_1(B_117) | ~r1_tarski(k1_relat_1(B_117), k1_relat_1(B_117)) | ~v2_funct_1(B_117) | ~v1_funct_1(B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(B_117) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_435, c_797])).
% 4.78/1.87  tff(c_850, plain, (![B_177]: (k9_relat_1(k2_funct_1(B_177), k2_relat_1(B_177))=k1_relat_1(B_177) | ~v2_funct_1(B_177) | ~v1_funct_1(B_177) | ~v1_relat_1(B_177))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_827])).
% 4.78/1.87  tff(c_862, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_850])).
% 4.78/1.87  tff(c_869, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_862])).
% 4.78/1.87  tff(c_769, plain, (![B_170, A_171]: (k10_relat_1(B_170, k9_relat_1(B_170, A_171))=A_171 | ~v2_funct_1(B_170) | ~r1_tarski(A_171, k1_relat_1(B_170)) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.87  tff(c_778, plain, (![B_172]: (k10_relat_1(B_172, k9_relat_1(B_172, k1_relat_1(B_172)))=k1_relat_1(B_172) | ~v2_funct_1(B_172) | ~v1_funct_1(B_172) | ~v1_relat_1(B_172))), inference(resolution, [status(thm)], [c_6, c_769])).
% 4.78/1.87  tff(c_889, plain, (![B_181]: (k10_relat_1(B_181, k2_relat_1(B_181))=k1_relat_1(B_181) | ~v2_funct_1(B_181) | ~v1_funct_1(B_181) | ~v1_relat_1(B_181) | ~v1_relat_1(B_181) | ~v1_relat_1(B_181))), inference(superposition, [status(thm), theory('equality')], [c_435, c_778])).
% 4.78/1.87  tff(c_20, plain, (![B_15, A_14]: (k9_relat_1(B_15, k10_relat_1(B_15, A_14))=A_14 | ~r1_tarski(A_14, k2_relat_1(B_15)) | ~v1_funct_1(B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.78/1.87  tff(c_609, plain, (![A_14]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_14))=A_14 | ~r1_tarski(A_14, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_593, c_20])).
% 4.78/1.87  tff(c_616, plain, (![A_14]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_14))=A_14 | ~r1_tarski(A_14, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_609])).
% 4.78/1.87  tff(c_821, plain, (![A_14]: (k9_relat_1(k2_funct_1('#skF_3'), A_14)=k10_relat_1('#skF_3', A_14) | ~r1_tarski(k10_relat_1('#skF_3', A_14), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~r1_tarski(A_14, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_797])).
% 4.78/1.87  tff(c_835, plain, (![A_14]: (k9_relat_1(k2_funct_1('#skF_3'), A_14)=k10_relat_1('#skF_3', A_14) | ~r1_tarski(k10_relat_1('#skF_3', A_14), k1_relat_1('#skF_3')) | ~r1_tarski(A_14, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_821])).
% 4.78/1.87  tff(c_896, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))=k10_relat_1('#skF_3', k2_relat_1('#skF_3')) | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_889, c_835])).
% 4.78/1.87  tff(c_915, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_74, c_74, c_64, c_761, c_6, c_593, c_6, c_869, c_593, c_593, c_896])).
% 4.78/1.87  tff(c_595, plain, (![B_148, A_149]: (k9_relat_1(B_148, k10_relat_1(B_148, A_149))=A_149 | ~r1_tarski(A_149, k2_relat_1(B_148)) | ~v1_funct_1(B_148) | ~v1_relat_1(B_148))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.78/1.87  tff(c_646, plain, (![B_153]: (k9_relat_1(B_153, k10_relat_1(B_153, k2_relat_1(B_153)))=k2_relat_1(B_153) | ~v1_funct_1(B_153) | ~v1_relat_1(B_153))), inference(resolution, [status(thm)], [c_6, c_595])).
% 4.78/1.87  tff(c_663, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))=k2_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_646])).
% 4.78/1.87  tff(c_674, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_593, c_663])).
% 4.78/1.87  tff(c_815, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k10_relat_1('#skF_3', '#skF_1') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_674, c_797])).
% 4.78/1.87  tff(c_833, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k10_relat_1('#skF_3', '#skF_1') | ~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_815])).
% 4.78/1.87  tff(c_842, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_833])).
% 4.78/1.87  tff(c_921, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_915, c_842])).
% 4.78/1.87  tff(c_925, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_921])).
% 4.78/1.87  tff(c_926, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k10_relat_1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_833])).
% 4.78/1.87  tff(c_977, plain, (![B_185]: (k9_relat_1(k2_funct_1(B_185), k2_relat_1(B_185))=k1_relat_1(B_185) | ~v2_funct_1(B_185) | ~v1_funct_1(B_185) | ~v1_relat_1(B_185))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_827])).
% 4.78/1.87  tff(c_989, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_593, c_977])).
% 4.78/1.87  tff(c_996, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_926, c_989])).
% 4.78/1.87  tff(c_927, plain, (r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_833])).
% 4.78/1.87  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.78/1.87  tff(c_941, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_927, c_2])).
% 4.78/1.87  tff(c_970, plain, (~r1_tarski(k1_relat_1('#skF_3'), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_941])).
% 4.78/1.87  tff(c_997, plain, (~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_996, c_970])).
% 4.78/1.87  tff(c_1004, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_997])).
% 4.78/1.87  tff(c_1005, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_941])).
% 4.78/1.87  tff(c_441, plain, (![B_118, A_119]: (r1_tarski(k1_relat_1(B_118), A_119) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.78/1.87  tff(c_448, plain, (![B_118, A_119]: (k1_relat_1(B_118)=A_119 | ~r1_tarski(A_119, k1_relat_1(B_118)) | ~v4_relat_1(B_118, A_119) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_441, c_2])).
% 4.78/1.87  tff(c_932, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_927, c_448])).
% 4.78/1.87  tff(c_940, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v4_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_932])).
% 4.78/1.87  tff(c_956, plain, (~v4_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_940])).
% 4.78/1.87  tff(c_1019, plain, (~v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1005, c_956])).
% 4.78/1.87  tff(c_1064, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_423, c_1019])).
% 4.78/1.87  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_1064])).
% 4.78/1.87  tff(c_1069, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_940])).
% 4.78/1.87  tff(c_24, plain, (![A_18, B_20]: (k9_relat_1(k2_funct_1(A_18), k9_relat_1(A_18, B_20))=B_20 | ~r1_tarski(B_20, k1_relat_1(A_18)) | ~v2_funct_1(A_18) | ~v1_funct_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.78/1.87  tff(c_952, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k10_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_926, c_24])).
% 4.78/1.87  tff(c_1213, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1069, c_952])).
% 4.78/1.87  tff(c_1214, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1213])).
% 4.78/1.87  tff(c_1402, plain, (![A_207, B_208]: (m1_subset_1(k2_funct_2(A_207, B_208), k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~m1_subset_1(B_208, k1_zfmisc_1(k2_zfmisc_1(A_207, A_207))) | ~v3_funct_2(B_208, A_207, A_207) | ~v1_funct_2(B_208, A_207, A_207) | ~v1_funct_1(B_208))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.87  tff(c_1434, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1122, c_1402])).
% 4.78/1.87  tff(c_1449, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_1434])).
% 4.78/1.87  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.78/1.87  tff(c_1478, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1449, c_8])).
% 4.78/1.87  tff(c_1503, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1478])).
% 4.78/1.87  tff(c_1505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1214, c_1503])).
% 4.78/1.87  tff(c_1507, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1213])).
% 4.78/1.87  tff(c_1175, plain, (![A_191, B_192]: (v3_funct_2(k2_funct_2(A_191, B_192), A_191, A_191) | ~m1_subset_1(B_192, k1_zfmisc_1(k2_zfmisc_1(A_191, A_191))) | ~v3_funct_2(B_192, A_191, A_191) | ~v1_funct_2(B_192, A_191, A_191) | ~v1_funct_1(B_192))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.87  tff(c_1177, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1175])).
% 4.78/1.87  tff(c_1180, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_1122, c_1177])).
% 4.78/1.87  tff(c_2328, plain, (![A_236, B_237]: (m1_subset_1(k2_funct_2(A_236, B_237), k1_zfmisc_1(k2_zfmisc_1(A_236, A_236))) | ~m1_subset_1(B_237, k1_zfmisc_1(k2_zfmisc_1(A_236, A_236))) | ~v3_funct_2(B_237, A_236, A_236) | ~v1_funct_2(B_237, A_236, A_236) | ~v1_funct_1(B_237))), inference(cnfTransformation, [status(thm)], [f_135])).
% 4.78/1.87  tff(c_2360, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1122, c_2328])).
% 4.78/1.87  tff(c_2375, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_62, c_60, c_58, c_2360])).
% 4.78/1.87  tff(c_34, plain, (![C_34, B_33, A_32]: (v2_funct_2(C_34, B_33) | ~v3_funct_2(C_34, A_32, B_33) | ~v1_funct_1(C_34) | ~m1_subset_1(C_34, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.78/1.87  tff(c_2388, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2375, c_34])).
% 4.78/1.87  tff(c_2419, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1180, c_2388])).
% 4.78/1.87  tff(c_26, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.87  tff(c_2426, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2375, c_26])).
% 4.78/1.87  tff(c_42, plain, (![B_36, A_35]: (k2_relat_1(B_36)=A_35 | ~v2_funct_2(B_36, A_35) | ~v5_relat_1(B_36, A_35) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.78/1.87  tff(c_2438, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2426, c_42])).
% 4.78/1.87  tff(c_2441, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_2419, c_2438])).
% 4.78/1.87  tff(c_1071, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1069, c_926])).
% 4.78/1.87  tff(c_28, plain, (![C_23, A_21, B_22]: (v4_relat_1(C_23, A_21) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.87  tff(c_2425, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2375, c_28])).
% 4.78/1.87  tff(c_2432, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2425, c_18])).
% 4.78/1.87  tff(c_2435, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_2432])).
% 4.78/1.87  tff(c_2490, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2435, c_16])).
% 4.78/1.87  tff(c_2500, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1507, c_2441, c_1071, c_2490])).
% 4.78/1.87  tff(c_460, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_457, c_18])).
% 4.78/1.87  tff(c_463, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_460])).
% 4.78/1.87  tff(c_467, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_463, c_16])).
% 4.78/1.87  tff(c_471, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_467])).
% 4.78/1.87  tff(c_606, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_593, c_471])).
% 4.78/1.87  tff(c_824, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_606, c_797])).
% 4.78/1.87  tff(c_837, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_824])).
% 4.78/1.87  tff(c_840, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_837])).
% 4.78/1.87  tff(c_2509, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2500, c_840])).
% 4.78/1.87  tff(c_2515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2509])).
% 4.78/1.87  tff(c_2517, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_837])).
% 4.78/1.87  tff(c_2529, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2517, c_448])).
% 4.78/1.87  tff(c_2537, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_457, c_2529])).
% 4.78/1.87  tff(c_22, plain, (![B_17, A_16]: (k10_relat_1(B_17, k9_relat_1(B_17, A_16))=A_16 | ~v2_funct_1(B_17) | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.78/1.87  tff(c_2546, plain, (![A_16]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_16))=A_16 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_16, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2537, c_22])).
% 4.78/1.87  tff(c_2671, plain, (![A_246]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_246))=A_246 | ~r1_tarski(A_246, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_761, c_2546])).
% 4.78/1.87  tff(c_695, plain, (![A_158, B_159, C_160, D_161]: (k8_relset_1(A_158, B_159, C_160, D_161)=k10_relat_1(C_160, D_161) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.87  tff(c_698, plain, (![D_161]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_161)=k10_relat_1('#skF_3', D_161))), inference(resolution, [status(thm)], [c_58, c_695])).
% 4.78/1.87  tff(c_691, plain, (![A_154, B_155, C_156, D_157]: (k7_relset_1(A_154, B_155, C_156, D_157)=k9_relat_1(C_156, D_157) | ~m1_subset_1(C_156, k1_zfmisc_1(k2_zfmisc_1(A_154, B_155))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.78/1.87  tff(c_694, plain, (![D_157]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_157)=k9_relat_1('#skF_3', D_157))), inference(resolution, [status(thm)], [c_58, c_691])).
% 4.78/1.87  tff(c_88, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.78/1.87  tff(c_92, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_58, c_88])).
% 4.78/1.87  tff(c_170, plain, (![B_66, A_67]: (k2_relat_1(B_66)=A_67 | ~v2_funct_2(B_66, A_67) | ~v5_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.78/1.87  tff(c_173, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_170])).
% 4.78/1.87  tff(c_176, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_173])).
% 4.78/1.87  tff(c_177, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_176])).
% 4.78/1.87  tff(c_248, plain, (![C_86, B_87, A_88]: (v2_funct_2(C_86, B_87) | ~v3_funct_2(C_86, A_88, B_87) | ~v1_funct_1(C_86) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.78/1.87  tff(c_251, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_248])).
% 4.78/1.87  tff(c_254, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_251])).
% 4.78/1.87  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_254])).
% 4.78/1.87  tff(c_257, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_176])).
% 4.78/1.87  tff(c_300, plain, (![B_96, A_97]: (k9_relat_1(B_96, k10_relat_1(B_96, A_97))=A_97 | ~r1_tarski(A_97, k2_relat_1(B_96)) | ~v1_funct_1(B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.78/1.87  tff(c_302, plain, (![A_97]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_97))=A_97 | ~r1_tarski(A_97, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_257, c_300])).
% 4.78/1.87  tff(c_312, plain, (![A_97]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_97))=A_97 | ~r1_tarski(A_97, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_64, c_302])).
% 4.78/1.87  tff(c_369, plain, (![A_100, B_101, C_102, D_103]: (k8_relset_1(A_100, B_101, C_102, D_103)=k10_relat_1(C_102, D_103) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.78/1.87  tff(c_372, plain, (![D_103]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_103)=k10_relat_1('#skF_3', D_103))), inference(resolution, [status(thm)], [c_58, c_369])).
% 4.78/1.87  tff(c_269, plain, (![A_89, B_90, C_91, D_92]: (k7_relset_1(A_89, B_90, C_91, D_92)=k9_relat_1(C_91, D_92) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.78/1.87  tff(c_272, plain, (![D_92]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_92)=k9_relat_1('#skF_3', D_92))), inference(resolution, [status(thm)], [c_58, c_269])).
% 4.78/1.87  tff(c_54, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_160])).
% 4.78/1.87  tff(c_75, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 4.78/1.87  tff(c_278, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_75])).
% 4.78/1.87  tff(c_373, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_372, c_278])).
% 4.78/1.87  tff(c_385, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_312, c_373])).
% 4.78/1.87  tff(c_389, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_385])).
% 4.78/1.87  tff(c_390, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 4.78/1.87  tff(c_699, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_694, c_390])).
% 4.78/1.87  tff(c_725, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_698, c_699])).
% 4.78/1.87  tff(c_2681, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2671, c_725])).
% 4.78/1.87  tff(c_2715, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_2681])).
% 4.78/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.78/1.87  
% 4.78/1.87  Inference rules
% 4.78/1.87  ----------------------
% 4.78/1.87  #Ref     : 0
% 4.78/1.87  #Sup     : 565
% 4.78/1.87  #Fact    : 0
% 4.78/1.87  #Define  : 0
% 4.78/1.87  #Split   : 19
% 4.78/1.87  #Chain   : 0
% 4.78/1.87  #Close   : 0
% 4.78/1.87  
% 4.78/1.87  Ordering : KBO
% 4.78/1.87  
% 4.78/1.87  Simplification rules
% 4.78/1.87  ----------------------
% 4.78/1.87  #Subsume      : 10
% 4.78/1.87  #Demod        : 914
% 4.78/1.87  #Tautology    : 263
% 4.78/1.87  #SimpNegUnit  : 3
% 4.78/1.87  #BackRed      : 66
% 4.78/1.87  
% 4.78/1.87  #Partial instantiations: 0
% 4.78/1.87  #Strategies tried      : 1
% 4.78/1.87  
% 4.78/1.87  Timing (in seconds)
% 4.78/1.87  ----------------------
% 4.78/1.87  Preprocessing        : 0.35
% 4.78/1.87  Parsing              : 0.19
% 4.78/1.87  CNF conversion       : 0.02
% 4.78/1.87  Main loop            : 0.71
% 4.78/1.87  Inferencing          : 0.26
% 4.78/1.87  Reduction            : 0.24
% 4.78/1.87  Demodulation         : 0.18
% 4.78/1.87  BG Simplification    : 0.03
% 4.78/1.87  Subsumption          : 0.12
% 4.78/1.87  Abstraction          : 0.03
% 4.78/1.87  MUC search           : 0.00
% 4.78/1.87  Cooper               : 0.00
% 4.78/1.87  Total                : 1.12
% 4.78/1.87  Index Insertion      : 0.00
% 4.78/1.87  Index Deletion       : 0.00
% 4.78/1.87  Index Matching       : 0.00
% 4.78/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
