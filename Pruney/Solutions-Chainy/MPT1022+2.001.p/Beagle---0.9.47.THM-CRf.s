%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:13 EST 2020

% Result     : Theorem 4.60s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :  183 (1364 expanded)
%              Number of leaves         :   49 ( 499 expanded)
%              Depth                    :   19
%              Number of atoms          :  361 (3851 expanded)
%              Number of equality atoms :   80 ( 771 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_170,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_48,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_121,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_155,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_145,axiom,(
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

tff(f_101,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_129,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_62,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_16,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_769,plain,(
    ! [B_196,A_197] :
      ( v1_relat_1(B_196)
      | ~ m1_subset_1(B_196,k1_zfmisc_1(A_197))
      | ~ v1_relat_1(A_197) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_775,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_769])).

tff(c_782,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_775])).

tff(c_70,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_66,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1421,plain,(
    ! [C_320,A_321,B_322] :
      ( v2_funct_1(C_320)
      | ~ v3_funct_2(C_320,A_321,B_322)
      | ~ v1_funct_1(C_320)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1428,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1421])).

tff(c_1436,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1428])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_755,plain,(
    ! [A_193,B_194] :
      ( r1_tarski(A_193,B_194)
      | ~ m1_subset_1(A_193,k1_zfmisc_1(B_194)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_767,plain,(
    ! [A_2] : r1_tarski(A_2,A_2) ),
    inference(resolution,[status(thm)],[c_71,c_755])).

tff(c_68,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1856,plain,(
    ! [A_404,B_405] :
      ( k2_funct_2(A_404,B_405) = k2_funct_1(B_405)
      | ~ m1_subset_1(B_405,k1_zfmisc_1(k2_zfmisc_1(A_404,A_404)))
      | ~ v3_funct_2(B_405,A_404,A_404)
      | ~ v1_funct_2(B_405,A_404,A_404)
      | ~ v1_funct_1(B_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_1863,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1856])).

tff(c_1871,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1863])).

tff(c_1725,plain,(
    ! [A_379,B_380] :
      ( v1_funct_1(k2_funct_2(A_379,B_380))
      | ~ m1_subset_1(B_380,k1_zfmisc_1(k2_zfmisc_1(A_379,A_379)))
      | ~ v3_funct_2(B_380,A_379,A_379)
      | ~ v1_funct_2(B_380,A_379,A_379)
      | ~ v1_funct_1(B_380) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1732,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1725])).

tff(c_1740,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1732])).

tff(c_1873,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1871,c_1740])).

tff(c_845,plain,(
    ! [C_210,B_211,A_212] :
      ( v5_relat_1(C_210,B_211)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_212,B_211))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_858,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_845])).

tff(c_955,plain,(
    ! [B_233,A_234] :
      ( k2_relat_1(B_233) = A_234
      | ~ v2_funct_2(B_233,A_234)
      | ~ v5_relat_1(B_233,A_234)
      | ~ v1_relat_1(B_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_961,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_858,c_955])).

tff(c_967,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_961])).

tff(c_968,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_1257,plain,(
    ! [C_300,B_301,A_302] :
      ( v2_funct_2(C_300,B_301)
      | ~ v3_funct_2(C_300,A_302,B_301)
      | ~ v1_funct_1(C_300)
      | ~ m1_subset_1(C_300,k1_zfmisc_1(k2_zfmisc_1(A_302,B_301))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_1264,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_1257])).

tff(c_1272,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1264])).

tff(c_1274,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_968,c_1272])).

tff(c_1275,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_20,plain,(
    ! [A_14] :
      ( k10_relat_1(A_14,k2_relat_1(A_14)) = k1_relat_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1283,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_20])).

tff(c_1289,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_1283])).

tff(c_1453,plain,(
    ! [B_327,A_328] :
      ( k9_relat_1(B_327,k10_relat_1(B_327,A_328)) = A_328
      | ~ r1_tarski(A_328,k2_relat_1(B_327))
      | ~ v1_funct_1(B_327)
      | ~ v1_relat_1(B_327) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1455,plain,(
    ! [A_328] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_328)) = A_328
      | ~ r1_tarski(A_328,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1275,c_1453])).

tff(c_1468,plain,(
    ! [A_329] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_329)) = A_329
      | ~ r1_tarski(A_329,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_70,c_1455])).

tff(c_1483,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1289,c_1468])).

tff(c_1497,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_1483])).

tff(c_1614,plain,(
    ! [A_363,B_364] :
      ( k9_relat_1(k2_funct_1(A_363),k9_relat_1(A_363,B_364)) = B_364
      | ~ r1_tarski(B_364,k1_relat_1(A_363))
      | ~ v2_funct_1(A_363)
      | ~ v1_funct_1(A_363)
      | ~ v1_relat_1(A_363) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1632,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1497,c_1614])).

tff(c_1650,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_70,c_1436,c_767,c_1632])).

tff(c_28,plain,(
    ! [A_21,B_23] :
      ( k9_relat_1(k2_funct_1(A_21),k9_relat_1(A_21,B_23)) = B_23
      | ~ r1_tarski(B_23,k1_relat_1(A_21))
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1662,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1650,c_28])).

tff(c_1880,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_3')))
    | ~ v2_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_1662])).

tff(c_1881,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1880])).

tff(c_2024,plain,(
    ! [A_437,B_438] :
      ( m1_subset_1(k2_funct_2(A_437,B_438),k1_zfmisc_1(k2_zfmisc_1(A_437,A_437)))
      | ~ m1_subset_1(B_438,k1_zfmisc_1(k2_zfmisc_1(A_437,A_437)))
      | ~ v3_funct_2(B_438,A_437,A_437)
      | ~ v1_funct_2(B_438,A_437,A_437)
      | ~ v1_funct_1(B_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2062,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_2024])).

tff(c_2079,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2062])).

tff(c_30,plain,(
    ! [C_26,A_24,B_25] :
      ( v1_relat_1(C_26)
      | ~ m1_subset_1(C_26,k1_zfmisc_1(k2_zfmisc_1(A_24,B_25))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2108,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2079,c_30])).

tff(c_2140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1881,c_2108])).

tff(c_2142,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1880])).

tff(c_2211,plain,(
    ! [A_451,B_452] :
      ( v3_funct_2(k2_funct_2(A_451,B_452),A_451,A_451)
      | ~ m1_subset_1(B_452,k1_zfmisc_1(k2_zfmisc_1(A_451,A_451)))
      | ~ v3_funct_2(B_452,A_451,A_451)
      | ~ v1_funct_2(B_452,A_451,A_451)
      | ~ v1_funct_1(B_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2216,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_2211])).

tff(c_2223,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_1871,c_2216])).

tff(c_2287,plain,(
    ! [A_474,B_475] :
      ( m1_subset_1(k2_funct_2(A_474,B_475),k1_zfmisc_1(k2_zfmisc_1(A_474,A_474)))
      | ~ m1_subset_1(B_475,k1_zfmisc_1(k2_zfmisc_1(A_474,A_474)))
      | ~ v3_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_2(B_475,A_474,A_474)
      | ~ v1_funct_1(B_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_2325,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1871,c_2287])).

tff(c_2342,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_64,c_2325])).

tff(c_40,plain,(
    ! [C_40,B_39,A_38] :
      ( v2_funct_2(C_40,B_39)
      | ~ v3_funct_2(C_40,A_38,B_39)
      | ~ v1_funct_1(C_40)
      | ~ m1_subset_1(C_40,k1_zfmisc_1(k2_zfmisc_1(A_38,B_39))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_2355,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2342,c_40])).

tff(c_2392,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1873,c_2223,c_2355])).

tff(c_32,plain,(
    ! [C_29,B_28,A_27] :
      ( v5_relat_1(C_29,B_28)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2399,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2342,c_32])).

tff(c_48,plain,(
    ! [B_42,A_41] :
      ( k2_relat_1(B_42) = A_41
      | ~ v2_funct_2(B_42,A_41)
      | ~ v5_relat_1(B_42,A_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_2419,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2399,c_48])).

tff(c_2422,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_2392,c_2419])).

tff(c_34,plain,(
    ! [C_29,A_27,B_28] :
      ( v4_relat_1(C_29,A_27)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2398,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_2342,c_34])).

tff(c_14,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(B_9),A_8)
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_945,plain,(
    ! [B_231,A_232] :
      ( k7_relat_1(B_231,A_232) = B_231
      | ~ r1_tarski(k1_relat_1(B_231),A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_953,plain,(
    ! [B_9,A_8] :
      ( k7_relat_1(B_9,A_8) = B_9
      | ~ v4_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_945])).

tff(c_2410,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_2398,c_953])).

tff(c_2416,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_2410])).

tff(c_18,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2493,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2416,c_18])).

tff(c_2497,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2142,c_2422,c_1650,c_2493])).

tff(c_889,plain,(
    ! [C_220,A_221,B_222] :
      ( v4_relat_1(C_220,A_221)
      | ~ m1_subset_1(C_220,k1_zfmisc_1(k2_zfmisc_1(A_221,B_222))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_902,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_889])).

tff(c_1308,plain,(
    ! [B_304,A_305] :
      ( k7_relat_1(B_304,A_305) = B_304
      | ~ v4_relat_1(B_304,A_305)
      | ~ v1_relat_1(B_304) ) ),
    inference(resolution,[status(thm)],[c_14,c_945])).

tff(c_1314,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_902,c_1308])).

tff(c_1323,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_1314])).

tff(c_1328,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1323,c_18])).

tff(c_1332,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_1275,c_1328])).

tff(c_1644,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1332,c_1614])).

tff(c_1658,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_70,c_1436,c_1644])).

tff(c_1666,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1650,c_1658])).

tff(c_1667,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1666])).

tff(c_2580,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2497,c_1667])).

tff(c_2586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_2580])).

tff(c_2587,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1666])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( k10_relat_1(B_20,k9_relat_1(B_20,A_19)) = A_19
      | ~ v2_funct_1(B_20)
      | ~ r1_tarski(A_19,k1_relat_1(B_20))
      | ~ v1_funct_1(B_20)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2595,plain,(
    ! [A_19] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_19)) = A_19
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_19,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2587,c_26])).

tff(c_2744,plain,(
    ! [A_487] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_487)) = A_487
      | ~ r1_tarski(A_487,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_782,c_70,c_1436,c_2595])).

tff(c_1379,plain,(
    ! [A_313,B_314,C_315,D_316] :
      ( k7_relset_1(A_313,B_314,C_315,D_316) = k9_relat_1(C_315,D_316)
      | ~ m1_subset_1(C_315,k1_zfmisc_1(k2_zfmisc_1(A_313,B_314))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1389,plain,(
    ! [D_316] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_316) = k9_relat_1('#skF_3',D_316) ),
    inference(resolution,[status(thm)],[c_64,c_1379])).

tff(c_1352,plain,(
    ! [A_308,B_309,C_310,D_311] :
      ( k8_relset_1(A_308,B_309,C_310,D_311) = k10_relat_1(C_310,D_311)
      | ~ m1_subset_1(C_310,k1_zfmisc_1(k2_zfmisc_1(A_308,B_309))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1362,plain,(
    ! [D_311] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_311) = k10_relat_1('#skF_3',D_311) ),
    inference(resolution,[status(thm)],[c_64,c_1352])).

tff(c_99,plain,(
    ! [B_56,A_57] :
      ( v1_relat_1(B_56)
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_57))
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_105,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_64,c_99])).

tff(c_112,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_105])).

tff(c_234,plain,(
    ! [C_82,B_83,A_84] :
      ( v5_relat_1(C_82,B_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_84,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_247,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_64,c_234])).

tff(c_369,plain,(
    ! [B_108,A_109] :
      ( k2_relat_1(B_108) = A_109
      | ~ v2_funct_2(B_108,A_109)
      | ~ v5_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_375,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_247,c_369])).

tff(c_381,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_375])).

tff(c_382,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_381])).

tff(c_567,plain,(
    ! [C_160,B_161,A_162] :
      ( v2_funct_2(C_160,B_161)
      | ~ v3_funct_2(C_160,A_162,B_161)
      | ~ v1_funct_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_162,B_161))) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_574,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_567])).

tff(c_582,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_574])).

tff(c_584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_582])).

tff(c_585,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_381])).

tff(c_716,plain,(
    ! [B_190,A_191] :
      ( k9_relat_1(B_190,k10_relat_1(B_190,A_191)) = A_191
      | ~ r1_tarski(A_191,k2_relat_1(B_190))
      | ~ v1_funct_1(B_190)
      | ~ v1_relat_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_718,plain,(
    ! [A_191] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_191)) = A_191
      | ~ r1_tarski(A_191,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_716])).

tff(c_731,plain,(
    ! [A_192] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_192)) = A_192
      | ~ r1_tarski(A_192,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_70,c_718])).

tff(c_693,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k8_relset_1(A_182,B_183,C_184,D_185) = k10_relat_1(C_184,D_185)
      | ~ m1_subset_1(C_184,k1_zfmisc_1(k2_zfmisc_1(A_182,B_183))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_703,plain,(
    ! [D_185] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_185) = k10_relat_1('#skF_3',D_185) ),
    inference(resolution,[status(thm)],[c_64,c_693])).

tff(c_630,plain,(
    ! [A_170,B_171,C_172,D_173] :
      ( k7_relset_1(A_170,B_171,C_172,D_173) = k9_relat_1(C_172,D_173)
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k2_zfmisc_1(A_170,B_171))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_640,plain,(
    ! [D_173] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_173) = k9_relat_1('#skF_3',D_173) ),
    inference(resolution,[status(thm)],[c_64,c_630])).

tff(c_60,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_84,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_642,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_84])).

tff(c_705,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_703,c_642])).

tff(c_737,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_731,c_705])).

tff(c_752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_737])).

tff(c_753,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1364,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1362,c_753])).

tff(c_1391,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1389,c_1364])).

tff(c_2756,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_1391])).

tff(c_2778,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2756])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.60/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  
% 4.60/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.60/1.82  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.60/1.82  
% 4.60/1.82  %Foreground sorts:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Background operators:
% 4.60/1.82  
% 4.60/1.82  
% 4.60/1.82  %Foreground operators:
% 4.60/1.82  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.60/1.82  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 4.60/1.82  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.60/1.82  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.60/1.82  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.82  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 4.60/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.60/1.82  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.60/1.82  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 4.60/1.82  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.60/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.60/1.82  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.60/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.60/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.60/1.82  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 4.60/1.82  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.60/1.82  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.60/1.82  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.60/1.82  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.60/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.60/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.60/1.82  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.60/1.82  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 4.60/1.82  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.60/1.82  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.60/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.60/1.82  
% 4.81/1.84  tff(f_170, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_funct_2)).
% 4.81/1.84  tff(f_48, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.81/1.84  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.81/1.84  tff(f_121, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_funct_2)).
% 4.81/1.84  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.81/1.84  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.81/1.84  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.81/1.84  tff(f_155, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 4.81/1.84  tff(f_145, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 4.81/1.84  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.81/1.84  tff(f_129, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_funct_2)).
% 4.81/1.84  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.81/1.84  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 4.81/1.84  tff(f_91, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 4.81/1.84  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.81/1.84  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.81/1.84  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.81/1.84  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.81/1.84  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t164_funct_1)).
% 4.81/1.84  tff(f_105, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 4.81/1.84  tff(f_109, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 4.81/1.84  tff(c_62, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.84  tff(c_16, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.81/1.84  tff(c_64, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.84  tff(c_769, plain, (![B_196, A_197]: (v1_relat_1(B_196) | ~m1_subset_1(B_196, k1_zfmisc_1(A_197)) | ~v1_relat_1(A_197))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.81/1.84  tff(c_775, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_769])).
% 4.81/1.84  tff(c_782, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_775])).
% 4.81/1.84  tff(c_70, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.84  tff(c_66, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.84  tff(c_1421, plain, (![C_320, A_321, B_322]: (v2_funct_1(C_320) | ~v3_funct_2(C_320, A_321, B_322) | ~v1_funct_1(C_320) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.81/1.84  tff(c_1428, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1421])).
% 4.81/1.84  tff(c_1436, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1428])).
% 4.81/1.84  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/1.84  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/1.84  tff(c_71, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.81/1.84  tff(c_755, plain, (![A_193, B_194]: (r1_tarski(A_193, B_194) | ~m1_subset_1(A_193, k1_zfmisc_1(B_194)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.81/1.84  tff(c_767, plain, (![A_2]: (r1_tarski(A_2, A_2))), inference(resolution, [status(thm)], [c_71, c_755])).
% 4.81/1.84  tff(c_68, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.84  tff(c_1856, plain, (![A_404, B_405]: (k2_funct_2(A_404, B_405)=k2_funct_1(B_405) | ~m1_subset_1(B_405, k1_zfmisc_1(k2_zfmisc_1(A_404, A_404))) | ~v3_funct_2(B_405, A_404, A_404) | ~v1_funct_2(B_405, A_404, A_404) | ~v1_funct_1(B_405))), inference(cnfTransformation, [status(thm)], [f_155])).
% 4.81/1.84  tff(c_1863, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1856])).
% 4.81/1.84  tff(c_1871, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1863])).
% 4.81/1.84  tff(c_1725, plain, (![A_379, B_380]: (v1_funct_1(k2_funct_2(A_379, B_380)) | ~m1_subset_1(B_380, k1_zfmisc_1(k2_zfmisc_1(A_379, A_379))) | ~v3_funct_2(B_380, A_379, A_379) | ~v1_funct_2(B_380, A_379, A_379) | ~v1_funct_1(B_380))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.81/1.84  tff(c_1732, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1725])).
% 4.81/1.84  tff(c_1740, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1732])).
% 4.81/1.84  tff(c_1873, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1871, c_1740])).
% 4.81/1.84  tff(c_845, plain, (![C_210, B_211, A_212]: (v5_relat_1(C_210, B_211) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_212, B_211))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.81/1.84  tff(c_858, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_845])).
% 4.81/1.84  tff(c_955, plain, (![B_233, A_234]: (k2_relat_1(B_233)=A_234 | ~v2_funct_2(B_233, A_234) | ~v5_relat_1(B_233, A_234) | ~v1_relat_1(B_233))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.81/1.84  tff(c_961, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_858, c_955])).
% 4.81/1.84  tff(c_967, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_961])).
% 4.81/1.84  tff(c_968, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_967])).
% 4.81/1.84  tff(c_1257, plain, (![C_300, B_301, A_302]: (v2_funct_2(C_300, B_301) | ~v3_funct_2(C_300, A_302, B_301) | ~v1_funct_1(C_300) | ~m1_subset_1(C_300, k1_zfmisc_1(k2_zfmisc_1(A_302, B_301))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.81/1.84  tff(c_1264, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_1257])).
% 4.81/1.84  tff(c_1272, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1264])).
% 4.81/1.84  tff(c_1274, plain, $false, inference(negUnitSimplification, [status(thm)], [c_968, c_1272])).
% 4.81/1.84  tff(c_1275, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_967])).
% 4.81/1.84  tff(c_20, plain, (![A_14]: (k10_relat_1(A_14, k2_relat_1(A_14))=k1_relat_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.81/1.84  tff(c_1283, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1275, c_20])).
% 4.81/1.84  tff(c_1289, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_1283])).
% 4.81/1.84  tff(c_1453, plain, (![B_327, A_328]: (k9_relat_1(B_327, k10_relat_1(B_327, A_328))=A_328 | ~r1_tarski(A_328, k2_relat_1(B_327)) | ~v1_funct_1(B_327) | ~v1_relat_1(B_327))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.81/1.84  tff(c_1455, plain, (![A_328]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_328))=A_328 | ~r1_tarski(A_328, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1275, c_1453])).
% 4.81/1.84  tff(c_1468, plain, (![A_329]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_329))=A_329 | ~r1_tarski(A_329, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_70, c_1455])).
% 4.81/1.84  tff(c_1483, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1289, c_1468])).
% 4.81/1.84  tff(c_1497, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_767, c_1483])).
% 4.81/1.84  tff(c_1614, plain, (![A_363, B_364]: (k9_relat_1(k2_funct_1(A_363), k9_relat_1(A_363, B_364))=B_364 | ~r1_tarski(B_364, k1_relat_1(A_363)) | ~v2_funct_1(A_363) | ~v1_funct_1(A_363) | ~v1_relat_1(A_363))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.81/1.84  tff(c_1632, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1497, c_1614])).
% 4.81/1.84  tff(c_1650, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_782, c_70, c_1436, c_767, c_1632])).
% 4.81/1.84  tff(c_28, plain, (![A_21, B_23]: (k9_relat_1(k2_funct_1(A_21), k9_relat_1(A_21, B_23))=B_23 | ~r1_tarski(B_23, k1_relat_1(A_21)) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.81/1.84  tff(c_1662, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1650, c_28])).
% 4.81/1.84  tff(c_1880, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_3'))) | ~v2_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1873, c_1662])).
% 4.81/1.84  tff(c_1881, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1880])).
% 4.81/1.84  tff(c_2024, plain, (![A_437, B_438]: (m1_subset_1(k2_funct_2(A_437, B_438), k1_zfmisc_1(k2_zfmisc_1(A_437, A_437))) | ~m1_subset_1(B_438, k1_zfmisc_1(k2_zfmisc_1(A_437, A_437))) | ~v3_funct_2(B_438, A_437, A_437) | ~v1_funct_2(B_438, A_437, A_437) | ~v1_funct_1(B_438))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.81/1.84  tff(c_2062, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_2024])).
% 4.81/1.84  tff(c_2079, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2062])).
% 4.81/1.84  tff(c_30, plain, (![C_26, A_24, B_25]: (v1_relat_1(C_26) | ~m1_subset_1(C_26, k1_zfmisc_1(k2_zfmisc_1(A_24, B_25))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.81/1.84  tff(c_2108, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2079, c_30])).
% 4.81/1.84  tff(c_2140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1881, c_2108])).
% 4.81/1.85  tff(c_2142, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_1880])).
% 4.81/1.85  tff(c_2211, plain, (![A_451, B_452]: (v3_funct_2(k2_funct_2(A_451, B_452), A_451, A_451) | ~m1_subset_1(B_452, k1_zfmisc_1(k2_zfmisc_1(A_451, A_451))) | ~v3_funct_2(B_452, A_451, A_451) | ~v1_funct_2(B_452, A_451, A_451) | ~v1_funct_1(B_452))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.81/1.85  tff(c_2216, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_2211])).
% 4.81/1.85  tff(c_2223, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_1871, c_2216])).
% 4.81/1.85  tff(c_2287, plain, (![A_474, B_475]: (m1_subset_1(k2_funct_2(A_474, B_475), k1_zfmisc_1(k2_zfmisc_1(A_474, A_474))) | ~m1_subset_1(B_475, k1_zfmisc_1(k2_zfmisc_1(A_474, A_474))) | ~v3_funct_2(B_475, A_474, A_474) | ~v1_funct_2(B_475, A_474, A_474) | ~v1_funct_1(B_475))), inference(cnfTransformation, [status(thm)], [f_145])).
% 4.81/1.85  tff(c_2325, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1871, c_2287])).
% 4.81/1.85  tff(c_2342, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_64, c_2325])).
% 4.81/1.85  tff(c_40, plain, (![C_40, B_39, A_38]: (v2_funct_2(C_40, B_39) | ~v3_funct_2(C_40, A_38, B_39) | ~v1_funct_1(C_40) | ~m1_subset_1(C_40, k1_zfmisc_1(k2_zfmisc_1(A_38, B_39))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.81/1.85  tff(c_2355, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2342, c_40])).
% 4.81/1.85  tff(c_2392, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1873, c_2223, c_2355])).
% 4.81/1.85  tff(c_32, plain, (![C_29, B_28, A_27]: (v5_relat_1(C_29, B_28) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.81/1.85  tff(c_2399, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2342, c_32])).
% 4.81/1.85  tff(c_48, plain, (![B_42, A_41]: (k2_relat_1(B_42)=A_41 | ~v2_funct_2(B_42, A_41) | ~v5_relat_1(B_42, A_41) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.81/1.85  tff(c_2419, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2399, c_48])).
% 4.81/1.85  tff(c_2422, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_2392, c_2419])).
% 4.81/1.85  tff(c_34, plain, (![C_29, A_27, B_28]: (v4_relat_1(C_29, A_27) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.81/1.85  tff(c_2398, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_2342, c_34])).
% 4.81/1.85  tff(c_14, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(B_9), A_8) | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.81/1.85  tff(c_945, plain, (![B_231, A_232]: (k7_relat_1(B_231, A_232)=B_231 | ~r1_tarski(k1_relat_1(B_231), A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.81/1.85  tff(c_953, plain, (![B_9, A_8]: (k7_relat_1(B_9, A_8)=B_9 | ~v4_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(resolution, [status(thm)], [c_14, c_945])).
% 4.81/1.85  tff(c_2410, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_2398, c_953])).
% 4.81/1.85  tff(c_2416, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_2410])).
% 4.81/1.85  tff(c_18, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.81/1.85  tff(c_2493, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2416, c_18])).
% 4.81/1.85  tff(c_2497, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2142, c_2422, c_1650, c_2493])).
% 4.81/1.85  tff(c_889, plain, (![C_220, A_221, B_222]: (v4_relat_1(C_220, A_221) | ~m1_subset_1(C_220, k1_zfmisc_1(k2_zfmisc_1(A_221, B_222))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.81/1.85  tff(c_902, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_889])).
% 4.81/1.85  tff(c_1308, plain, (![B_304, A_305]: (k7_relat_1(B_304, A_305)=B_304 | ~v4_relat_1(B_304, A_305) | ~v1_relat_1(B_304))), inference(resolution, [status(thm)], [c_14, c_945])).
% 4.81/1.85  tff(c_1314, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_902, c_1308])).
% 4.81/1.85  tff(c_1323, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_1314])).
% 4.81/1.85  tff(c_1328, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1323, c_18])).
% 4.81/1.85  tff(c_1332, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_782, c_1275, c_1328])).
% 4.81/1.85  tff(c_1644, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1332, c_1614])).
% 4.81/1.85  tff(c_1658, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_70, c_1436, c_1644])).
% 4.81/1.85  tff(c_1666, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1650, c_1658])).
% 4.81/1.85  tff(c_1667, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_1666])).
% 4.81/1.85  tff(c_2580, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2497, c_1667])).
% 4.81/1.85  tff(c_2586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_767, c_2580])).
% 4.81/1.85  tff(c_2587, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1666])).
% 4.81/1.85  tff(c_26, plain, (![B_20, A_19]: (k10_relat_1(B_20, k9_relat_1(B_20, A_19))=A_19 | ~v2_funct_1(B_20) | ~r1_tarski(A_19, k1_relat_1(B_20)) | ~v1_funct_1(B_20) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.81/1.85  tff(c_2595, plain, (![A_19]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_19))=A_19 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_19, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_2587, c_26])).
% 4.81/1.85  tff(c_2744, plain, (![A_487]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_487))=A_487 | ~r1_tarski(A_487, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_782, c_70, c_1436, c_2595])).
% 4.81/1.85  tff(c_1379, plain, (![A_313, B_314, C_315, D_316]: (k7_relset_1(A_313, B_314, C_315, D_316)=k9_relat_1(C_315, D_316) | ~m1_subset_1(C_315, k1_zfmisc_1(k2_zfmisc_1(A_313, B_314))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.81/1.85  tff(c_1389, plain, (![D_316]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_316)=k9_relat_1('#skF_3', D_316))), inference(resolution, [status(thm)], [c_64, c_1379])).
% 4.81/1.85  tff(c_1352, plain, (![A_308, B_309, C_310, D_311]: (k8_relset_1(A_308, B_309, C_310, D_311)=k10_relat_1(C_310, D_311) | ~m1_subset_1(C_310, k1_zfmisc_1(k2_zfmisc_1(A_308, B_309))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.81/1.85  tff(c_1362, plain, (![D_311]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_311)=k10_relat_1('#skF_3', D_311))), inference(resolution, [status(thm)], [c_64, c_1352])).
% 4.81/1.85  tff(c_99, plain, (![B_56, A_57]: (v1_relat_1(B_56) | ~m1_subset_1(B_56, k1_zfmisc_1(A_57)) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.81/1.85  tff(c_105, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_64, c_99])).
% 4.81/1.85  tff(c_112, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_105])).
% 4.81/1.85  tff(c_234, plain, (![C_82, B_83, A_84]: (v5_relat_1(C_82, B_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_84, B_83))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 4.81/1.85  tff(c_247, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_64, c_234])).
% 4.81/1.85  tff(c_369, plain, (![B_108, A_109]: (k2_relat_1(B_108)=A_109 | ~v2_funct_2(B_108, A_109) | ~v5_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.81/1.85  tff(c_375, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_247, c_369])).
% 4.81/1.85  tff(c_381, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_375])).
% 4.81/1.85  tff(c_382, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_381])).
% 4.81/1.85  tff(c_567, plain, (![C_160, B_161, A_162]: (v2_funct_2(C_160, B_161) | ~v3_funct_2(C_160, A_162, B_161) | ~v1_funct_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_162, B_161))))), inference(cnfTransformation, [status(thm)], [f_121])).
% 4.81/1.85  tff(c_574, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_64, c_567])).
% 4.81/1.85  tff(c_582, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_574])).
% 4.81/1.85  tff(c_584, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_582])).
% 4.81/1.85  tff(c_585, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_381])).
% 4.81/1.85  tff(c_716, plain, (![B_190, A_191]: (k9_relat_1(B_190, k10_relat_1(B_190, A_191))=A_191 | ~r1_tarski(A_191, k2_relat_1(B_190)) | ~v1_funct_1(B_190) | ~v1_relat_1(B_190))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.81/1.85  tff(c_718, plain, (![A_191]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_191))=A_191 | ~r1_tarski(A_191, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_585, c_716])).
% 4.81/1.85  tff(c_731, plain, (![A_192]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_192))=A_192 | ~r1_tarski(A_192, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_70, c_718])).
% 4.81/1.85  tff(c_693, plain, (![A_182, B_183, C_184, D_185]: (k8_relset_1(A_182, B_183, C_184, D_185)=k10_relat_1(C_184, D_185) | ~m1_subset_1(C_184, k1_zfmisc_1(k2_zfmisc_1(A_182, B_183))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.81/1.85  tff(c_703, plain, (![D_185]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_185)=k10_relat_1('#skF_3', D_185))), inference(resolution, [status(thm)], [c_64, c_693])).
% 4.81/1.85  tff(c_630, plain, (![A_170, B_171, C_172, D_173]: (k7_relset_1(A_170, B_171, C_172, D_173)=k9_relat_1(C_172, D_173) | ~m1_subset_1(C_172, k1_zfmisc_1(k2_zfmisc_1(A_170, B_171))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.81/1.85  tff(c_640, plain, (![D_173]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_173)=k9_relat_1('#skF_3', D_173))), inference(resolution, [status(thm)], [c_64, c_630])).
% 4.81/1.85  tff(c_60, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_170])).
% 4.81/1.85  tff(c_84, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_60])).
% 4.81/1.85  tff(c_642, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_84])).
% 4.81/1.85  tff(c_705, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_703, c_642])).
% 4.81/1.85  tff(c_737, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_731, c_705])).
% 4.81/1.85  tff(c_752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_737])).
% 4.81/1.85  tff(c_753, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_60])).
% 4.81/1.85  tff(c_1364, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1362, c_753])).
% 4.81/1.85  tff(c_1391, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1389, c_1364])).
% 4.81/1.85  tff(c_2756, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2744, c_1391])).
% 4.81/1.85  tff(c_2778, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_2756])).
% 4.81/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.85  
% 4.81/1.85  Inference rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Ref     : 0
% 4.81/1.85  #Sup     : 556
% 4.81/1.85  #Fact    : 0
% 4.81/1.85  #Define  : 0
% 4.81/1.85  #Split   : 10
% 4.81/1.85  #Chain   : 0
% 4.81/1.85  #Close   : 0
% 4.81/1.85  
% 4.81/1.85  Ordering : KBO
% 4.81/1.85  
% 4.81/1.85  Simplification rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Subsume      : 18
% 4.81/1.85  #Demod        : 480
% 4.81/1.85  #Tautology    : 215
% 4.81/1.85  #SimpNegUnit  : 5
% 4.81/1.85  #BackRed      : 21
% 4.81/1.85  
% 4.81/1.85  #Partial instantiations: 0
% 4.81/1.85  #Strategies tried      : 1
% 4.81/1.85  
% 4.81/1.85  Timing (in seconds)
% 4.81/1.85  ----------------------
% 4.81/1.85  Preprocessing        : 0.37
% 4.81/1.85  Parsing              : 0.20
% 4.81/1.85  CNF conversion       : 0.02
% 4.81/1.85  Main loop            : 0.70
% 4.81/1.85  Inferencing          : 0.26
% 4.81/1.85  Reduction            : 0.24
% 4.81/1.85  Demodulation         : 0.16
% 4.81/1.85  BG Simplification    : 0.04
% 4.81/1.85  Subsumption          : 0.11
% 4.81/1.85  Abstraction          : 0.04
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.12
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
