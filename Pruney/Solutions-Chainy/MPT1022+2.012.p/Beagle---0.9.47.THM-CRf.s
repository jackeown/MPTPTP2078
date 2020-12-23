%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:14 EST 2020

% Result     : Theorem 4.06s
% Output     : CNFRefutation 4.06s
% Verified   : 
% Statistics : Number of formulae       :  174 (1186 expanded)
%              Number of leaves         :   45 ( 433 expanded)
%              Depth                    :   18
%              Number of atoms          :  345 (3357 expanded)
%              Number of equality atoms :   80 ( 686 expanded)
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

tff(f_164,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_123,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_149,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_139,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => ( v1_funct_1(k2_funct_2(A,B))
        & v1_funct_2(k2_funct_2(A,B),A,A)
        & v3_funct_2(k2_funct_2(A,B),A,A)
        & m1_subset_1(k2_funct_2(A,B),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(f_99,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(c_58,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_60,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_79,plain,(
    ! [B_46,A_47] :
      ( v1_relat_1(B_46)
      | ~ m1_subset_1(B_46,k1_zfmisc_1(A_47))
      | ~ v1_relat_1(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_82,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_60,c_79])).

tff(c_85,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_66,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_62,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_686,plain,(
    ! [C_160,A_161,B_162] :
      ( v2_funct_1(C_160)
      | ~ v3_funct_2(C_160,A_161,B_162)
      | ~ v1_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_161,B_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_689,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_686])).

tff(c_692,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_689])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_419,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_423,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_419])).

tff(c_519,plain,(
    ! [B_131,A_132] :
      ( k2_relat_1(B_131) = A_132
      | ~ v2_funct_2(B_131,A_132)
      | ~ v5_relat_1(B_131,A_132)
      | ~ v1_relat_1(B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_522,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_423,c_519])).

tff(c_525,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_522])).

tff(c_526,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_614,plain,(
    ! [C_150,B_151,A_152] :
      ( v2_funct_2(C_150,B_151)
      | ~ v3_funct_2(C_150,A_152,B_151)
      | ~ v1_funct_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_152,B_151))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_617,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_614])).

tff(c_620,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_617])).

tff(c_622,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_526,c_620])).

tff(c_623,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_632,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_18])).

tff(c_638,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_632])).

tff(c_709,plain,(
    ! [B_168,A_169] :
      ( k9_relat_1(B_168,k10_relat_1(B_168,A_169)) = A_169
      | ~ r1_tarski(A_169,k2_relat_1(B_168))
      | ~ v1_funct_1(B_168)
      | ~ v1_relat_1(B_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_711,plain,(
    ! [A_169] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_169)) = A_169
      | ~ r1_tarski(A_169,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_709])).

tff(c_740,plain,(
    ! [A_170] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_170)) = A_170
      | ~ r1_tarski(A_170,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66,c_711])).

tff(c_755,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_638,c_740])).

tff(c_769,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_755])).

tff(c_835,plain,(
    ! [A_177,B_178] :
      ( k9_relat_1(k2_funct_1(A_177),k9_relat_1(A_177,B_178)) = B_178
      | ~ r1_tarski(B_178,k1_relat_1(A_177))
      | ~ v2_funct_1(A_177)
      | ~ v1_funct_1(A_177)
      | ~ v1_relat_1(A_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_853,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_769,c_835])).

tff(c_869,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66,c_692,c_6,c_853])).

tff(c_444,plain,(
    ! [B_122,A_123] :
      ( k2_relat_1(k7_relat_1(B_122,A_123)) = k9_relat_1(B_122,A_123)
      | ~ v1_relat_1(B_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_961,plain,(
    ! [B_186,A_187] :
      ( k10_relat_1(k7_relat_1(B_186,A_187),k9_relat_1(B_186,A_187)) = k1_relat_1(k7_relat_1(B_186,A_187))
      | ~ v1_relat_1(k7_relat_1(B_186,A_187))
      | ~ v1_relat_1(B_186) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_444,c_18])).

tff(c_973,plain,
    ( k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3')) = k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'),'#skF_1'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_961])).

tff(c_1322,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_973])).

tff(c_64,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1112,plain,(
    ! [A_188,B_189] :
      ( k2_funct_2(A_188,B_189) = k2_funct_1(B_189)
      | ~ m1_subset_1(B_189,k1_zfmisc_1(k2_zfmisc_1(A_188,A_188)))
      | ~ v3_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_2(B_189,A_188,A_188)
      | ~ v1_funct_1(B_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_1115,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1112])).

tff(c_1118,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1115])).

tff(c_1446,plain,(
    ! [A_205,B_206] :
      ( m1_subset_1(k2_funct_2(A_205,B_206),k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ m1_subset_1(B_206,k1_zfmisc_1(k2_zfmisc_1(A_205,A_205)))
      | ~ v3_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_2(B_206,A_205,A_205)
      | ~ v1_funct_1(B_206) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1478,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_1446])).

tff(c_1493,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_1478])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1522,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_1493,c_8])).

tff(c_1547,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1522])).

tff(c_1549,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1322,c_1547])).

tff(c_1551,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_973])).

tff(c_954,plain,(
    ! [A_184,B_185] :
      ( v1_funct_1(k2_funct_2(A_184,B_185))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(k2_zfmisc_1(A_184,A_184)))
      | ~ v3_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_2(B_185,A_184,A_184)
      | ~ v1_funct_1(B_185) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_957,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_954])).

tff(c_960,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_957])).

tff(c_1131,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1118,c_960])).

tff(c_1217,plain,(
    ! [A_192,B_193] :
      ( v3_funct_2(k2_funct_2(A_192,B_193),A_192,A_192)
      | ~ m1_subset_1(B_193,k1_zfmisc_1(k2_zfmisc_1(A_192,A_192)))
      | ~ v3_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_2(B_193,A_192,A_192)
      | ~ v1_funct_1(B_193) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_1219,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_1217])).

tff(c_1222,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_1118,c_1219])).

tff(c_1972,plain,(
    ! [A_217,B_218] :
      ( m1_subset_1(k2_funct_2(A_217,B_218),k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ m1_subset_1(B_218,k1_zfmisc_1(k2_zfmisc_1(A_217,A_217)))
      | ~ v3_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_2(B_218,A_217,A_217)
      | ~ v1_funct_1(B_218) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2004,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1118,c_1972])).

tff(c_2019,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_62,c_60,c_2004])).

tff(c_36,plain,(
    ! [C_35,B_34,A_33] :
      ( v2_funct_2(C_35,B_34)
      | ~ v3_funct_2(C_35,A_33,B_34)
      | ~ v1_funct_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2032,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2019,c_36])).

tff(c_2063,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1131,c_1222,c_2032])).

tff(c_28,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2070,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2019,c_28])).

tff(c_44,plain,(
    ! [B_37,A_36] :
      ( k2_relat_1(B_37) = A_36
      | ~ v2_funct_2(B_37,A_36)
      | ~ v5_relat_1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2082,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2070,c_44])).

tff(c_2085,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_2063,c_2082])).

tff(c_30,plain,(
    ! [C_24,A_22,B_23] :
      ( v4_relat_1(C_24,A_22)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2069,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2019,c_30])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_460,plain,(
    ! [B_124,A_125] :
      ( k7_relat_1(B_124,A_125) = B_124
      | ~ r1_tarski(k1_relat_1(B_124),A_125)
      | ~ v1_relat_1(B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_468,plain,(
    ! [B_7,A_6] :
      ( k7_relat_1(B_7,A_6) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_460])).

tff(c_2076,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2069,c_468])).

tff(c_2079,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_2076])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2122,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2079,c_16])).

tff(c_2128,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1551,c_2085,c_869,c_2122])).

tff(c_424,plain,(
    ! [C_114,A_115,B_116] :
      ( v4_relat_1(C_114,A_115)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_428,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_424])).

tff(c_482,plain,(
    ! [B_127,A_128] :
      ( k7_relat_1(B_127,A_128) = B_127
      | ~ v4_relat_1(B_127,A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(resolution,[status(thm)],[c_12,c_460])).

tff(c_488,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_428,c_482])).

tff(c_492,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_488])).

tff(c_496,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_492,c_16])).

tff(c_500,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_496])).

tff(c_625,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_500])).

tff(c_862,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_625,c_835])).

tff(c_875,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66,c_692,c_862])).

tff(c_885,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_875])).

tff(c_886,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_885])).

tff(c_2140,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_886])).

tff(c_2148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2140])).

tff(c_2149,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_885])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k10_relat_1(B_18,k9_relat_1(B_18,A_17)) = A_17
      | ~ v2_funct_1(B_18)
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2157,plain,(
    ! [A_17] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_17)) = A_17
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2149,c_24])).

tff(c_2299,plain,(
    ! [A_228] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_228)) = A_228
      | ~ r1_tarski(A_228,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66,c_692,c_2157])).

tff(c_693,plain,(
    ! [A_163,B_164,C_165,D_166] :
      ( k8_relset_1(A_163,B_164,C_165,D_166) = k10_relat_1(C_165,D_166)
      | ~ m1_subset_1(C_165,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_696,plain,(
    ! [D_166] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_166) = k10_relat_1('#skF_3',D_166) ),
    inference(resolution,[status(thm)],[c_60,c_693])).

tff(c_649,plain,(
    ! [A_153,B_154,C_155,D_156] :
      ( k7_relset_1(A_153,B_154,C_155,D_156) = k9_relat_1(C_155,D_156)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_652,plain,(
    ! [D_156] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_156) = k9_relat_1('#skF_3',D_156) ),
    inference(resolution,[status(thm)],[c_60,c_649])).

tff(c_98,plain,(
    ! [C_50,B_51,A_52] :
      ( v5_relat_1(C_50,B_51)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_52,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_102,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_98])).

tff(c_149,plain,(
    ! [B_66,A_67] :
      ( k2_relat_1(B_66) = A_67
      | ~ v2_funct_2(B_66,A_67)
      | ~ v5_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_152,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_149])).

tff(c_155,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_152])).

tff(c_156,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_155])).

tff(c_275,plain,(
    ! [C_90,B_91,A_92] :
      ( v2_funct_2(C_90,B_91)
      | ~ v3_funct_2(C_90,A_92,B_91)
      | ~ v1_funct_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_278,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_60,c_275])).

tff(c_281,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_278])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_156,c_281])).

tff(c_284,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_155])).

tff(c_369,plain,(
    ! [B_106,A_107] :
      ( k9_relat_1(B_106,k10_relat_1(B_106,A_107)) = A_107
      | ~ r1_tarski(A_107,k2_relat_1(B_106))
      | ~ v1_funct_1(B_106)
      | ~ v1_relat_1(B_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_371,plain,(
    ! [A_107] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_107)) = A_107
      | ~ r1_tarski(A_107,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_369])).

tff(c_384,plain,(
    ! [A_108] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_108)) = A_108
      | ~ r1_tarski(A_108,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_66,c_371])).

tff(c_351,plain,(
    ! [A_101,B_102,C_103,D_104] :
      ( k8_relset_1(A_101,B_102,C_103,D_104) = k10_relat_1(C_103,D_104)
      | ~ m1_subset_1(C_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_354,plain,(
    ! [D_104] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_104) = k10_relat_1('#skF_3',D_104) ),
    inference(resolution,[status(thm)],[c_60,c_351])).

tff(c_286,plain,(
    ! [A_93,B_94,C_95,D_96] :
      ( k7_relset_1(A_93,B_94,C_95,D_96) = k9_relat_1(C_95,D_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_289,plain,(
    ! [D_96] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_96) = k9_relat_1('#skF_3',D_96) ),
    inference(resolution,[status(thm)],[c_60,c_286])).

tff(c_56,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_86,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_305,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_86])).

tff(c_359,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_305])).

tff(c_390,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_359])).

tff(c_405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_390])).

tff(c_406,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_653,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_652,c_406])).

tff(c_698,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_696,c_653])).

tff(c_2311,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2299,c_698])).

tff(c_2337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2311])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.06/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.74  
% 4.06/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.74  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.06/1.74  
% 4.06/1.74  %Foreground sorts:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Background operators:
% 4.06/1.74  
% 4.06/1.74  
% 4.06/1.74  %Foreground operators:
% 4.06/1.74  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.06/1.74  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.06/1.74  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.06/1.74  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.06/1.74  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.06/1.74  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.06/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.06/1.74  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.06/1.74  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.06/1.74  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.06/1.74  tff('#skF_2', type, '#skF_2': $i).
% 4.06/1.74  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.06/1.74  tff('#skF_3', type, '#skF_3': $i).
% 4.06/1.74  tff('#skF_1', type, '#skF_1': $i).
% 4.06/1.74  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.06/1.74  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.06/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.06/1.74  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.06/1.74  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.06/1.74  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.06/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.06/1.74  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.06/1.74  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.06/1.74  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.06/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.06/1.74  
% 4.06/1.77  tff(f_164, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 4.06/1.77  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.06/1.77  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.06/1.77  tff(f_115, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.06/1.77  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.06/1.77  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.06/1.77  tff(f_123, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.06/1.77  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.06/1.77  tff(f_68, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 4.06/1.77  tff(f_89, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 4.06/1.77  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.06/1.77  tff(f_149, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.06/1.77  tff(f_139, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.06/1.77  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.06/1.77  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.06/1.77  tff(f_78, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.06/1.77  tff(f_103, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.06/1.77  tff(f_99, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.06/1.77  tff(c_58, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.06/1.77  tff(c_60, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_79, plain, (![B_46, A_47]: (v1_relat_1(B_46) | ~m1_subset_1(B_46, k1_zfmisc_1(A_47)) | ~v1_relat_1(A_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.77  tff(c_82, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_60, c_79])).
% 4.06/1.77  tff(c_85, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 4.06/1.77  tff(c_66, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_62, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_686, plain, (![C_160, A_161, B_162]: (v2_funct_1(C_160) | ~v3_funct_2(C_160, A_161, B_162) | ~v1_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_161, B_162))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.06/1.77  tff(c_689, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_686])).
% 4.06/1.77  tff(c_692, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_689])).
% 4.06/1.77  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.06/1.77  tff(c_419, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.77  tff(c_423, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_419])).
% 4.06/1.77  tff(c_519, plain, (![B_131, A_132]: (k2_relat_1(B_131)=A_132 | ~v2_funct_2(B_131, A_132) | ~v5_relat_1(B_131, A_132) | ~v1_relat_1(B_131))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.06/1.77  tff(c_522, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_423, c_519])).
% 4.06/1.77  tff(c_525, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_522])).
% 4.06/1.77  tff(c_526, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_525])).
% 4.06/1.77  tff(c_614, plain, (![C_150, B_151, A_152]: (v2_funct_2(C_150, B_151) | ~v3_funct_2(C_150, A_152, B_151) | ~v1_funct_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_152, B_151))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.06/1.77  tff(c_617, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_614])).
% 4.06/1.77  tff(c_620, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_617])).
% 4.06/1.77  tff(c_622, plain, $false, inference(negUnitSimplification, [status(thm)], [c_526, c_620])).
% 4.06/1.77  tff(c_623, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_525])).
% 4.06/1.77  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.06/1.77  tff(c_632, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_623, c_18])).
% 4.06/1.77  tff(c_638, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_632])).
% 4.06/1.77  tff(c_709, plain, (![B_168, A_169]: (k9_relat_1(B_168, k10_relat_1(B_168, A_169))=A_169 | ~r1_tarski(A_169, k2_relat_1(B_168)) | ~v1_funct_1(B_168) | ~v1_relat_1(B_168))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.77  tff(c_711, plain, (![A_169]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_169))=A_169 | ~r1_tarski(A_169, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_623, c_709])).
% 4.06/1.77  tff(c_740, plain, (![A_170]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_170))=A_170 | ~r1_tarski(A_170, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66, c_711])).
% 4.06/1.77  tff(c_755, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_638, c_740])).
% 4.06/1.77  tff(c_769, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_755])).
% 4.06/1.77  tff(c_835, plain, (![A_177, B_178]: (k9_relat_1(k2_funct_1(A_177), k9_relat_1(A_177, B_178))=B_178 | ~r1_tarski(B_178, k1_relat_1(A_177)) | ~v2_funct_1(A_177) | ~v1_funct_1(A_177) | ~v1_relat_1(A_177))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.06/1.77  tff(c_853, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_769, c_835])).
% 4.06/1.77  tff(c_869, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66, c_692, c_6, c_853])).
% 4.06/1.77  tff(c_444, plain, (![B_122, A_123]: (k2_relat_1(k7_relat_1(B_122, A_123))=k9_relat_1(B_122, A_123) | ~v1_relat_1(B_122))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.77  tff(c_961, plain, (![B_186, A_187]: (k10_relat_1(k7_relat_1(B_186, A_187), k9_relat_1(B_186, A_187))=k1_relat_1(k7_relat_1(B_186, A_187)) | ~v1_relat_1(k7_relat_1(B_186, A_187)) | ~v1_relat_1(B_186))), inference(superposition, [status(thm), theory('equality')], [c_444, c_18])).
% 4.06/1.77  tff(c_973, plain, (k10_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3'))=k1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_869, c_961])).
% 4.06/1.77  tff(c_1322, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_973])).
% 4.06/1.77  tff(c_64, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_1112, plain, (![A_188, B_189]: (k2_funct_2(A_188, B_189)=k2_funct_1(B_189) | ~m1_subset_1(B_189, k1_zfmisc_1(k2_zfmisc_1(A_188, A_188))) | ~v3_funct_2(B_189, A_188, A_188) | ~v1_funct_2(B_189, A_188, A_188) | ~v1_funct_1(B_189))), inference(cnfTransformation, [status(thm)], [f_149])).
% 4.06/1.77  tff(c_1115, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1112])).
% 4.06/1.77  tff(c_1118, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1115])).
% 4.06/1.77  tff(c_1446, plain, (![A_205, B_206]: (m1_subset_1(k2_funct_2(A_205, B_206), k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~m1_subset_1(B_206, k1_zfmisc_1(k2_zfmisc_1(A_205, A_205))) | ~v3_funct_2(B_206, A_205, A_205) | ~v1_funct_2(B_206, A_205, A_205) | ~v1_funct_1(B_206))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.06/1.77  tff(c_1478, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_1446])).
% 4.06/1.77  tff(c_1493, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_1478])).
% 4.06/1.77  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.06/1.77  tff(c_1522, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_1493, c_8])).
% 4.06/1.77  tff(c_1547, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1522])).
% 4.06/1.77  tff(c_1549, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1322, c_1547])).
% 4.06/1.77  tff(c_1551, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_973])).
% 4.06/1.77  tff(c_954, plain, (![A_184, B_185]: (v1_funct_1(k2_funct_2(A_184, B_185)) | ~m1_subset_1(B_185, k1_zfmisc_1(k2_zfmisc_1(A_184, A_184))) | ~v3_funct_2(B_185, A_184, A_184) | ~v1_funct_2(B_185, A_184, A_184) | ~v1_funct_1(B_185))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.06/1.77  tff(c_957, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_954])).
% 4.06/1.77  tff(c_960, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_957])).
% 4.06/1.77  tff(c_1131, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1118, c_960])).
% 4.06/1.77  tff(c_1217, plain, (![A_192, B_193]: (v3_funct_2(k2_funct_2(A_192, B_193), A_192, A_192) | ~m1_subset_1(B_193, k1_zfmisc_1(k2_zfmisc_1(A_192, A_192))) | ~v3_funct_2(B_193, A_192, A_192) | ~v1_funct_2(B_193, A_192, A_192) | ~v1_funct_1(B_193))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.06/1.77  tff(c_1219, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_1217])).
% 4.06/1.77  tff(c_1222, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_1118, c_1219])).
% 4.06/1.77  tff(c_1972, plain, (![A_217, B_218]: (m1_subset_1(k2_funct_2(A_217, B_218), k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~m1_subset_1(B_218, k1_zfmisc_1(k2_zfmisc_1(A_217, A_217))) | ~v3_funct_2(B_218, A_217, A_217) | ~v1_funct_2(B_218, A_217, A_217) | ~v1_funct_1(B_218))), inference(cnfTransformation, [status(thm)], [f_139])).
% 4.06/1.77  tff(c_2004, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1118, c_1972])).
% 4.06/1.77  tff(c_2019, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_62, c_60, c_2004])).
% 4.06/1.77  tff(c_36, plain, (![C_35, B_34, A_33]: (v2_funct_2(C_35, B_34) | ~v3_funct_2(C_35, A_33, B_34) | ~v1_funct_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.06/1.77  tff(c_2032, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2019, c_36])).
% 4.06/1.77  tff(c_2063, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1131, c_1222, c_2032])).
% 4.06/1.77  tff(c_28, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.77  tff(c_2070, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2019, c_28])).
% 4.06/1.77  tff(c_44, plain, (![B_37, A_36]: (k2_relat_1(B_37)=A_36 | ~v2_funct_2(B_37, A_36) | ~v5_relat_1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.06/1.77  tff(c_2082, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2070, c_44])).
% 4.06/1.77  tff(c_2085, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_2063, c_2082])).
% 4.06/1.77  tff(c_30, plain, (![C_24, A_22, B_23]: (v4_relat_1(C_24, A_22) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.77  tff(c_2069, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2019, c_30])).
% 4.06/1.77  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.06/1.77  tff(c_460, plain, (![B_124, A_125]: (k7_relat_1(B_124, A_125)=B_124 | ~r1_tarski(k1_relat_1(B_124), A_125) | ~v1_relat_1(B_124))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.06/1.77  tff(c_468, plain, (![B_7, A_6]: (k7_relat_1(B_7, A_6)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_460])).
% 4.06/1.77  tff(c_2076, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2069, c_468])).
% 4.06/1.77  tff(c_2079, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_2076])).
% 4.06/1.77  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.06/1.77  tff(c_2122, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2079, c_16])).
% 4.06/1.77  tff(c_2128, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1551, c_2085, c_869, c_2122])).
% 4.06/1.77  tff(c_424, plain, (![C_114, A_115, B_116]: (v4_relat_1(C_114, A_115) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.77  tff(c_428, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_424])).
% 4.06/1.77  tff(c_482, plain, (![B_127, A_128]: (k7_relat_1(B_127, A_128)=B_127 | ~v4_relat_1(B_127, A_128) | ~v1_relat_1(B_127))), inference(resolution, [status(thm)], [c_12, c_460])).
% 4.06/1.77  tff(c_488, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_428, c_482])).
% 4.06/1.77  tff(c_492, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_488])).
% 4.06/1.77  tff(c_496, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_492, c_16])).
% 4.06/1.77  tff(c_500, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_496])).
% 4.06/1.77  tff(c_625, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_500])).
% 4.06/1.77  tff(c_862, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_625, c_835])).
% 4.06/1.77  tff(c_875, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66, c_692, c_862])).
% 4.06/1.77  tff(c_885, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_869, c_875])).
% 4.06/1.77  tff(c_886, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_885])).
% 4.06/1.77  tff(c_2140, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2128, c_886])).
% 4.06/1.77  tff(c_2148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2140])).
% 4.06/1.77  tff(c_2149, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_885])).
% 4.06/1.77  tff(c_24, plain, (![B_18, A_17]: (k10_relat_1(B_18, k9_relat_1(B_18, A_17))=A_17 | ~v2_funct_1(B_18) | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.06/1.77  tff(c_2157, plain, (![A_17]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_17))=A_17 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_17, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2149, c_24])).
% 4.06/1.77  tff(c_2299, plain, (![A_228]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_228))=A_228 | ~r1_tarski(A_228, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66, c_692, c_2157])).
% 4.06/1.77  tff(c_693, plain, (![A_163, B_164, C_165, D_166]: (k8_relset_1(A_163, B_164, C_165, D_166)=k10_relat_1(C_165, D_166) | ~m1_subset_1(C_165, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.06/1.77  tff(c_696, plain, (![D_166]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_166)=k10_relat_1('#skF_3', D_166))), inference(resolution, [status(thm)], [c_60, c_693])).
% 4.06/1.77  tff(c_649, plain, (![A_153, B_154, C_155, D_156]: (k7_relset_1(A_153, B_154, C_155, D_156)=k9_relat_1(C_155, D_156) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.06/1.77  tff(c_652, plain, (![D_156]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_156)=k9_relat_1('#skF_3', D_156))), inference(resolution, [status(thm)], [c_60, c_649])).
% 4.06/1.77  tff(c_98, plain, (![C_50, B_51, A_52]: (v5_relat_1(C_50, B_51) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_52, B_51))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.06/1.77  tff(c_102, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_60, c_98])).
% 4.06/1.77  tff(c_149, plain, (![B_66, A_67]: (k2_relat_1(B_66)=A_67 | ~v2_funct_2(B_66, A_67) | ~v5_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.06/1.77  tff(c_152, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_149])).
% 4.06/1.77  tff(c_155, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_152])).
% 4.06/1.77  tff(c_156, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_155])).
% 4.06/1.77  tff(c_275, plain, (![C_90, B_91, A_92]: (v2_funct_2(C_90, B_91) | ~v3_funct_2(C_90, A_92, B_91) | ~v1_funct_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.06/1.77  tff(c_278, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_60, c_275])).
% 4.06/1.77  tff(c_281, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_278])).
% 4.06/1.77  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_156, c_281])).
% 4.06/1.77  tff(c_284, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_155])).
% 4.06/1.77  tff(c_369, plain, (![B_106, A_107]: (k9_relat_1(B_106, k10_relat_1(B_106, A_107))=A_107 | ~r1_tarski(A_107, k2_relat_1(B_106)) | ~v1_funct_1(B_106) | ~v1_relat_1(B_106))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.06/1.77  tff(c_371, plain, (![A_107]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_107))=A_107 | ~r1_tarski(A_107, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_284, c_369])).
% 4.06/1.77  tff(c_384, plain, (![A_108]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_108))=A_108 | ~r1_tarski(A_108, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_66, c_371])).
% 4.06/1.77  tff(c_351, plain, (![A_101, B_102, C_103, D_104]: (k8_relset_1(A_101, B_102, C_103, D_104)=k10_relat_1(C_103, D_104) | ~m1_subset_1(C_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.06/1.77  tff(c_354, plain, (![D_104]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_104)=k10_relat_1('#skF_3', D_104))), inference(resolution, [status(thm)], [c_60, c_351])).
% 4.06/1.77  tff(c_286, plain, (![A_93, B_94, C_95, D_96]: (k7_relset_1(A_93, B_94, C_95, D_96)=k9_relat_1(C_95, D_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.06/1.77  tff(c_289, plain, (![D_96]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_96)=k9_relat_1('#skF_3', D_96))), inference(resolution, [status(thm)], [c_60, c_286])).
% 4.06/1.77  tff(c_56, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_164])).
% 4.06/1.77  tff(c_86, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 4.06/1.77  tff(c_305, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_289, c_86])).
% 4.06/1.77  tff(c_359, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_305])).
% 4.06/1.77  tff(c_390, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_384, c_359])).
% 4.06/1.77  tff(c_405, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_390])).
% 4.06/1.77  tff(c_406, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 4.06/1.77  tff(c_653, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_652, c_406])).
% 4.06/1.77  tff(c_698, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_696, c_653])).
% 4.06/1.77  tff(c_2311, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2299, c_698])).
% 4.06/1.77  tff(c_2337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_2311])).
% 4.06/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.06/1.77  
% 4.06/1.77  Inference rules
% 4.06/1.77  ----------------------
% 4.06/1.77  #Ref     : 0
% 4.06/1.77  #Sup     : 485
% 4.06/1.77  #Fact    : 0
% 4.06/1.77  #Define  : 0
% 4.06/1.77  #Split   : 16
% 4.41/1.77  #Chain   : 0
% 4.41/1.77  #Close   : 0
% 4.41/1.77  
% 4.41/1.77  Ordering : KBO
% 4.41/1.77  
% 4.41/1.77  Simplification rules
% 4.41/1.77  ----------------------
% 4.41/1.77  #Subsume      : 15
% 4.41/1.77  #Demod        : 667
% 4.41/1.77  #Tautology    : 243
% 4.41/1.77  #SimpNegUnit  : 4
% 4.41/1.77  #BackRed      : 37
% 4.41/1.77  
% 4.41/1.77  #Partial instantiations: 0
% 4.41/1.77  #Strategies tried      : 1
% 4.41/1.77  
% 4.41/1.77  Timing (in seconds)
% 4.41/1.77  ----------------------
% 4.41/1.77  Preprocessing        : 0.35
% 4.41/1.77  Parsing              : 0.19
% 4.41/1.77  CNF conversion       : 0.02
% 4.41/1.77  Main loop            : 0.62
% 4.41/1.77  Inferencing          : 0.21
% 4.41/1.77  Reduction            : 0.20
% 4.41/1.77  Demodulation         : 0.15
% 4.41/1.77  BG Simplification    : 0.03
% 4.41/1.77  Subsumption          : 0.11
% 4.41/1.77  Abstraction          : 0.03
% 4.41/1.77  MUC search           : 0.00
% 4.41/1.77  Cooper               : 0.00
% 4.41/1.77  Total                : 1.02
% 4.41/1.77  Index Insertion      : 0.00
% 4.41/1.77  Index Deletion       : 0.00
% 4.41/1.77  Index Matching       : 0.00
% 4.41/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
