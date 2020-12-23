%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:15 EST 2020

% Result     : Theorem 6.70s
% Output     : CNFRefutation 6.87s
% Verified   : 
% Statistics : Number of formulae       :  174 ( 764 expanded)
%              Number of leaves         :   45 ( 293 expanded)
%              Depth                    :   20
%              Number of atoms          :  342 (2291 expanded)
%              Number of equality atoms :   76 ( 456 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_165,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,A)
          & v3_funct_2(C,A,A)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ( r1_tarski(B,A)
         => ( k7_relset_1(A,A,C,k8_relset_1(A,A,C,B)) = B
            & k8_relset_1(A,A,C,k7_relset_1(A,A,C,B)) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_funct_2)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_96,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_124,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_150,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_140,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => k9_relat_1(B,A) = k10_relat_1(k2_funct_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t154_funct_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_104,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k8_relset_1(A,B,C,D) = k10_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

tff(c_60,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_990,plain,(
    ! [B_206,A_207] :
      ( v1_relat_1(B_206)
      | ~ m1_subset_1(B_206,k1_zfmisc_1(A_207))
      | ~ v1_relat_1(A_207) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_996,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_990])).

tff(c_1000,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_996])).

tff(c_68,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_64,plain,(
    v3_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_1905,plain,(
    ! [C_338,A_339,B_340] :
      ( v2_funct_1(C_338)
      | ~ v3_funct_2(C_338,A_339,B_340)
      | ~ v1_funct_1(C_338)
      | ~ m1_subset_1(C_338,k1_zfmisc_1(k2_zfmisc_1(A_339,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1912,plain,
    ( v2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1905])).

tff(c_1916,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1912])).

tff(c_1065,plain,(
    ! [C_219,B_220,A_221] :
      ( v5_relat_1(C_219,B_220)
      | ~ m1_subset_1(C_219,k1_zfmisc_1(k2_zfmisc_1(A_221,B_220))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1074,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1065])).

tff(c_1145,plain,(
    ! [B_236,A_237] :
      ( k2_relat_1(B_236) = A_237
      | ~ v2_funct_2(B_236,A_237)
      | ~ v5_relat_1(B_236,A_237)
      | ~ v1_relat_1(B_236) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1151,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1074,c_1145])).

tff(c_1157,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1151])).

tff(c_1158,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1157])).

tff(c_1391,plain,(
    ! [C_282,B_283,A_284] :
      ( v2_funct_2(C_282,B_283)
      | ~ v3_funct_2(C_282,A_284,B_283)
      | ~ v1_funct_1(C_282)
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_284,B_283))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1398,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1391])).

tff(c_1402,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_1398])).

tff(c_1404,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1158,c_1402])).

tff(c_1405,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1157])).

tff(c_18,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1414,plain,
    ( k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1405,c_18])).

tff(c_1420,plain,(
    k10_relat_1('#skF_3','#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1414])).

tff(c_1044,plain,(
    ! [C_213,A_214,B_215] :
      ( v4_relat_1(C_213,A_214)
      | ~ m1_subset_1(C_213,k1_zfmisc_1(k2_zfmisc_1(A_214,B_215))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1053,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_1044])).

tff(c_1100,plain,(
    ! [B_231,A_232] :
      ( k7_relat_1(B_231,A_232) = B_231
      | ~ v4_relat_1(B_231,A_232)
      | ~ v1_relat_1(B_231) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1106,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1053,c_1100])).

tff(c_1112,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1106])).

tff(c_16,plain,(
    ! [B_11,A_10] :
      ( k2_relat_1(k7_relat_1(B_11,A_10)) = k9_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1116,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_16])).

tff(c_1120,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_1116])).

tff(c_1407,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1405,c_1120])).

tff(c_66,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_3152,plain,(
    ! [A_418,B_419] :
      ( k2_funct_2(A_418,B_419) = k2_funct_1(B_419)
      | ~ m1_subset_1(B_419,k1_zfmisc_1(k2_zfmisc_1(A_418,A_418)))
      | ~ v3_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_2(B_419,A_418,A_418)
      | ~ v1_funct_1(B_419) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_3159,plain,
    ( k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_3152])).

tff(c_3163,plain,(
    k2_funct_2('#skF_1','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_3159])).

tff(c_2220,plain,(
    ! [A_385,B_386] :
      ( v1_funct_1(k2_funct_2(A_385,B_386))
      | ~ m1_subset_1(B_386,k1_zfmisc_1(k2_zfmisc_1(A_385,A_385)))
      | ~ v3_funct_2(B_386,A_385,A_385)
      | ~ v1_funct_2(B_386,A_385,A_385)
      | ~ v1_funct_1(B_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2227,plain,
    ( v1_funct_1(k2_funct_2('#skF_1','#skF_3'))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2220])).

tff(c_2231,plain,(
    v1_funct_1(k2_funct_2('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_2227])).

tff(c_3164,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3163,c_2231])).

tff(c_4152,plain,(
    ! [A_448,B_449] :
      ( v3_funct_2(k2_funct_2(A_448,B_449),A_448,A_448)
      | ~ m1_subset_1(B_449,k1_zfmisc_1(k2_zfmisc_1(A_448,A_448)))
      | ~ v3_funct_2(B_449,A_448,A_448)
      | ~ v1_funct_2(B_449,A_448,A_448)
      | ~ v1_funct_1(B_449) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_4157,plain,
    ( v3_funct_2(k2_funct_2('#skF_1','#skF_3'),'#skF_1','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_4152])).

tff(c_4161,plain,(
    v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_3163,c_4157])).

tff(c_5215,plain,(
    ! [A_469,B_470] :
      ( m1_subset_1(k2_funct_2(A_469,B_470),k1_zfmisc_1(k2_zfmisc_1(A_469,A_469)))
      | ~ m1_subset_1(B_470,k1_zfmisc_1(k2_zfmisc_1(A_469,A_469)))
      | ~ v3_funct_2(B_470,A_469,A_469)
      | ~ v1_funct_2(B_470,A_469,A_469)
      | ~ v1_funct_1(B_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_5250,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3163,c_5215])).

tff(c_5266,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_64,c_62,c_5250])).

tff(c_38,plain,(
    ! [C_36,B_35,A_34] :
      ( v2_funct_2(C_36,B_35)
      | ~ v3_funct_2(C_36,A_34,B_35)
      | ~ v1_funct_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_5279,plain,
    ( v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v3_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5266,c_38])).

tff(c_5313,plain,(
    v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3164,c_4161,c_5279])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_5295,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_5266,c_12])).

tff(c_5323,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5295])).

tff(c_30,plain,(
    ! [C_25,B_24,A_23] :
      ( v5_relat_1(C_25,B_24)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5319,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5266,c_30])).

tff(c_46,plain,(
    ! [B_38,A_37] :
      ( k2_relat_1(B_38) = A_37
      | ~ v2_funct_2(B_38,A_37)
      | ~ v5_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_5327,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5319,c_46])).

tff(c_5330,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v2_funct_2(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5323,c_5327])).

tff(c_5791,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5313,c_5330])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5320,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_5266,c_32])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5333,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_5320,c_20])).

tff(c_5336,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5323,c_5333])).

tff(c_5380,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5336,c_16])).

tff(c_5386,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5323,c_5380])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1637,plain,(
    ! [B_320,A_321] :
      ( k9_relat_1(B_320,k10_relat_1(B_320,A_321)) = A_321
      | ~ r1_tarski(A_321,k2_relat_1(B_320))
      | ~ v1_funct_1(B_320)
      | ~ v1_relat_1(B_320) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1644,plain,(
    ! [A_321] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_321)) = A_321
      | ~ r1_tarski(A_321,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1405,c_1637])).

tff(c_1655,plain,(
    ! [A_322] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_322)) = A_322
      | ~ r1_tarski(A_322,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_68,c_1644])).

tff(c_1680,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1655])).

tff(c_1700,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1680])).

tff(c_1441,plain,(
    ! [B_289,A_290] :
      ( r1_tarski(k9_relat_1(B_289,k10_relat_1(B_289,A_290)),A_290)
      | ~ v1_funct_1(B_289)
      | ~ v1_relat_1(B_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1457,plain,
    ( r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_1')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1420,c_1441])).

tff(c_1466,plain,(
    r1_tarski(k9_relat_1('#skF_3',k1_relat_1('#skF_3')),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_68,c_1457])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1472,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_1466,c_2])).

tff(c_1494,plain,(
    ~ r1_tarski('#skF_1',k9_relat_1('#skF_3',k1_relat_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1472])).

tff(c_1703,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1700,c_1494])).

tff(c_1707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1703])).

tff(c_1708,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1472])).

tff(c_1474,plain,(
    ! [B_291,A_292] :
      ( k10_relat_1(k2_funct_1(B_291),A_292) = k9_relat_1(B_291,A_292)
      | ~ v2_funct_1(B_291)
      | ~ v1_funct_1(B_291)
      | ~ v1_relat_1(B_291) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_22,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k9_relat_1(B_16,k10_relat_1(B_16,A_15)),A_15)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_5499,plain,(
    ! [B_474,A_475] :
      ( r1_tarski(k9_relat_1(k2_funct_1(B_474),k9_relat_1(B_474,A_475)),A_475)
      | ~ v1_funct_1(k2_funct_1(B_474))
      | ~ v1_relat_1(k2_funct_1(B_474))
      | ~ v2_funct_1(B_474)
      | ~ v1_funct_1(B_474)
      | ~ v1_relat_1(B_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1474,c_22])).

tff(c_5572,plain,
    ( r1_tarski(k9_relat_1(k2_funct_1('#skF_3'),'#skF_1'),k1_relat_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1708,c_5499])).

tff(c_5603,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_68,c_1916,c_5323,c_3164,c_5386,c_5572])).

tff(c_5793,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5791,c_5603])).

tff(c_28,plain,(
    ! [B_22,A_21] :
      ( k10_relat_1(B_22,k9_relat_1(B_22,A_21)) = A_21
      | ~ v2_funct_1(B_22)
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_5869,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5793,c_28])).

tff(c_5877,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_68,c_1916,c_1420,c_1407,c_5869])).

tff(c_5948,plain,(
    ! [A_21] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_21)) = A_21
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5877,c_28])).

tff(c_6674,plain,(
    ! [A_494] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_494)) = A_494
      | ~ r1_tarski(A_494,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1000,c_68,c_1916,c_5948])).

tff(c_1953,plain,(
    ! [A_349,B_350,C_351,D_352] :
      ( k7_relset_1(A_349,B_350,C_351,D_352) = k9_relat_1(C_351,D_352)
      | ~ m1_subset_1(C_351,k1_zfmisc_1(k2_zfmisc_1(A_349,B_350))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1960,plain,(
    ! [D_352] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_352) = k9_relat_1('#skF_3',D_352) ),
    inference(resolution,[status(thm)],[c_62,c_1953])).

tff(c_1934,plain,(
    ! [A_344,B_345,C_346,D_347] :
      ( k8_relset_1(A_344,B_345,C_346,D_347) = k10_relat_1(C_346,D_347)
      | ~ m1_subset_1(C_346,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_1941,plain,(
    ! [D_347] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_347) = k10_relat_1('#skF_3',D_347) ),
    inference(resolution,[status(thm)],[c_62,c_1934])).

tff(c_83,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_89,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_62,c_83])).

tff(c_93,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_89])).

tff(c_133,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_142,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_133])).

tff(c_243,plain,(
    ! [B_82,A_83] :
      ( k2_relat_1(B_82) = A_83
      | ~ v2_funct_2(B_82,A_83)
      | ~ v5_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_249,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_142,c_243])).

tff(c_255,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_249])).

tff(c_256,plain,(
    ~ v2_funct_2('#skF_3','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_501,plain,(
    ! [C_134,B_135,A_136] :
      ( v2_funct_2(C_134,B_135)
      | ~ v3_funct_2(C_134,A_136,B_135)
      | ~ v1_funct_1(C_134)
      | ~ m1_subset_1(C_134,k1_zfmisc_1(k2_zfmisc_1(A_136,B_135))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_508,plain,
    ( v2_funct_2('#skF_3','#skF_1')
    | ~ v3_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_501])).

tff(c_512,plain,(
    v2_funct_2('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_64,c_508])).

tff(c_514,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_256,c_512])).

tff(c_515,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_934,plain,(
    ! [B_203,A_204] :
      ( k9_relat_1(B_203,k10_relat_1(B_203,A_204)) = A_204
      | ~ r1_tarski(A_204,k2_relat_1(B_203))
      | ~ v1_funct_1(B_203)
      | ~ v1_relat_1(B_203) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_941,plain,(
    ! [A_204] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_204)) = A_204
      | ~ r1_tarski(A_204,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_934])).

tff(c_952,plain,(
    ! [A_205] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_205)) = A_205
      | ~ r1_tarski(A_205,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_68,c_941])).

tff(c_903,plain,(
    ! [A_194,B_195,C_196,D_197] :
      ( k8_relset_1(A_194,B_195,C_196,D_197) = k10_relat_1(C_196,D_197)
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_194,B_195))) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_910,plain,(
    ! [D_197] : k8_relset_1('#skF_1','#skF_1','#skF_3',D_197) = k10_relat_1('#skF_3',D_197) ),
    inference(resolution,[status(thm)],[c_62,c_903])).

tff(c_885,plain,(
    ! [A_189,B_190,C_191,D_192] :
      ( k7_relset_1(A_189,B_190,C_191,D_192) = k9_relat_1(C_191,D_192)
      | ~ m1_subset_1(C_191,k1_zfmisc_1(k2_zfmisc_1(A_189,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_892,plain,(
    ! [D_192] : k7_relset_1('#skF_1','#skF_1','#skF_3',D_192) = k9_relat_1('#skF_3',D_192) ),
    inference(resolution,[status(thm)],[c_62,c_885])).

tff(c_58,plain,
    ( k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2'
    | k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_82,plain,(
    k7_relset_1('#skF_1','#skF_1','#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_893,plain,(
    k9_relat_1('#skF_3',k8_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_892,c_82])).

tff(c_920,plain,(
    k9_relat_1('#skF_3',k10_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_910,c_893])).

tff(c_958,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_952,c_920])).

tff(c_987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_958])).

tff(c_988,plain,(
    k8_relset_1('#skF_1','#skF_1','#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_1942,plain,(
    k10_relat_1('#skF_3',k7_relset_1('#skF_1','#skF_1','#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1941,c_988])).

tff(c_1965,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1960,c_1942])).

tff(c_6696,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6674,c_1965])).

tff(c_6752,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_6696])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:05:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.70/2.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.41  
% 6.79/2.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.79/2.41  %$ v3_funct_2 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k8_relset_1 > k7_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > k2_funct_2 > k10_relat_1 > #nlpp > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.79/2.41  
% 6.79/2.41  %Foreground sorts:
% 6.79/2.41  
% 6.79/2.41  
% 6.79/2.41  %Background operators:
% 6.79/2.41  
% 6.79/2.41  
% 6.79/2.41  %Foreground operators:
% 6.79/2.41  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.79/2.41  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.79/2.41  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.79/2.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.79/2.41  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.79/2.41  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 6.79/2.41  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 6.79/2.41  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.79/2.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.79/2.41  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 6.79/2.41  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.79/2.41  tff('#skF_2', type, '#skF_2': $i).
% 6.79/2.41  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.79/2.41  tff('#skF_3', type, '#skF_3': $i).
% 6.79/2.41  tff('#skF_1', type, '#skF_1': $i).
% 6.79/2.41  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.79/2.41  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.79/2.41  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.79/2.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.79/2.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.79/2.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.79/2.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.79/2.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.79/2.41  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.79/2.41  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 6.79/2.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.79/2.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.79/2.41  
% 6.87/2.44  tff(f_165, negated_conjecture, ~(![A, B, C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r1_tarski(B, A) => ((k7_relset_1(A, A, C, k8_relset_1(A, A, C, B)) = B) & (k8_relset_1(A, A, C, k7_relset_1(A, A, C, B)) = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_funct_2)).
% 6.87/2.44  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.87/2.44  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.87/2.44  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 6.87/2.44  tff(f_96, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.87/2.44  tff(f_124, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.87/2.44  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 6.87/2.44  tff(f_58, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.87/2.44  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 6.87/2.44  tff(f_150, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 6.87/2.44  tff(f_140, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 6.87/2.44  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.87/2.44  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_funct_1)).
% 6.87/2.44  tff(f_64, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_funct_1)).
% 6.87/2.44  tff(f_80, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => (k9_relat_1(B, A) = k10_relat_1(k2_funct_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t154_funct_1)).
% 6.87/2.44  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 6.87/2.44  tff(f_100, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 6.87/2.44  tff(f_104, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k8_relset_1(A, B, C, D) = k10_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k8_relset_1)).
% 6.87/2.44  tff(c_60, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.87/2.44  tff(c_62, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_990, plain, (![B_206, A_207]: (v1_relat_1(B_206) | ~m1_subset_1(B_206, k1_zfmisc_1(A_207)) | ~v1_relat_1(A_207))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.87/2.44  tff(c_996, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_990])).
% 6.87/2.44  tff(c_1000, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_996])).
% 6.87/2.44  tff(c_68, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_64, plain, (v3_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_1905, plain, (![C_338, A_339, B_340]: (v2_funct_1(C_338) | ~v3_funct_2(C_338, A_339, B_340) | ~v1_funct_1(C_338) | ~m1_subset_1(C_338, k1_zfmisc_1(k2_zfmisc_1(A_339, B_340))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.87/2.44  tff(c_1912, plain, (v2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1905])).
% 6.87/2.44  tff(c_1916, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1912])).
% 6.87/2.44  tff(c_1065, plain, (![C_219, B_220, A_221]: (v5_relat_1(C_219, B_220) | ~m1_subset_1(C_219, k1_zfmisc_1(k2_zfmisc_1(A_221, B_220))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.87/2.44  tff(c_1074, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1065])).
% 6.87/2.44  tff(c_1145, plain, (![B_236, A_237]: (k2_relat_1(B_236)=A_237 | ~v2_funct_2(B_236, A_237) | ~v5_relat_1(B_236, A_237) | ~v1_relat_1(B_236))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.87/2.44  tff(c_1151, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1074, c_1145])).
% 6.87/2.44  tff(c_1157, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1151])).
% 6.87/2.44  tff(c_1158, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_1157])).
% 6.87/2.44  tff(c_1391, plain, (![C_282, B_283, A_284]: (v2_funct_2(C_282, B_283) | ~v3_funct_2(C_282, A_284, B_283) | ~v1_funct_1(C_282) | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_284, B_283))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.87/2.44  tff(c_1398, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1391])).
% 6.87/2.44  tff(c_1402, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_1398])).
% 6.87/2.44  tff(c_1404, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1158, c_1402])).
% 6.87/2.44  tff(c_1405, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_1157])).
% 6.87/2.44  tff(c_18, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.87/2.44  tff(c_1414, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1405, c_18])).
% 6.87/2.44  tff(c_1420, plain, (k10_relat_1('#skF_3', '#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1414])).
% 6.87/2.44  tff(c_1044, plain, (![C_213, A_214, B_215]: (v4_relat_1(C_213, A_214) | ~m1_subset_1(C_213, k1_zfmisc_1(k2_zfmisc_1(A_214, B_215))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.87/2.44  tff(c_1053, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_1044])).
% 6.87/2.44  tff(c_1100, plain, (![B_231, A_232]: (k7_relat_1(B_231, A_232)=B_231 | ~v4_relat_1(B_231, A_232) | ~v1_relat_1(B_231))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.87/2.44  tff(c_1106, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1053, c_1100])).
% 6.87/2.44  tff(c_1112, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1106])).
% 6.87/2.44  tff(c_16, plain, (![B_11, A_10]: (k2_relat_1(k7_relat_1(B_11, A_10))=k9_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.87/2.44  tff(c_1116, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1112, c_16])).
% 6.87/2.44  tff(c_1120, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_1116])).
% 6.87/2.44  tff(c_1407, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1405, c_1120])).
% 6.87/2.44  tff(c_66, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_3152, plain, (![A_418, B_419]: (k2_funct_2(A_418, B_419)=k2_funct_1(B_419) | ~m1_subset_1(B_419, k1_zfmisc_1(k2_zfmisc_1(A_418, A_418))) | ~v3_funct_2(B_419, A_418, A_418) | ~v1_funct_2(B_419, A_418, A_418) | ~v1_funct_1(B_419))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.87/2.44  tff(c_3159, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_3152])).
% 6.87/2.44  tff(c_3163, plain, (k2_funct_2('#skF_1', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_3159])).
% 6.87/2.44  tff(c_2220, plain, (![A_385, B_386]: (v1_funct_1(k2_funct_2(A_385, B_386)) | ~m1_subset_1(B_386, k1_zfmisc_1(k2_zfmisc_1(A_385, A_385))) | ~v3_funct_2(B_386, A_385, A_385) | ~v1_funct_2(B_386, A_385, A_385) | ~v1_funct_1(B_386))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.87/2.44  tff(c_2227, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3')) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2220])).
% 6.87/2.44  tff(c_2231, plain, (v1_funct_1(k2_funct_2('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_2227])).
% 6.87/2.44  tff(c_3164, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3163, c_2231])).
% 6.87/2.44  tff(c_4152, plain, (![A_448, B_449]: (v3_funct_2(k2_funct_2(A_448, B_449), A_448, A_448) | ~m1_subset_1(B_449, k1_zfmisc_1(k2_zfmisc_1(A_448, A_448))) | ~v3_funct_2(B_449, A_448, A_448) | ~v1_funct_2(B_449, A_448, A_448) | ~v1_funct_1(B_449))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.87/2.44  tff(c_4157, plain, (v3_funct_2(k2_funct_2('#skF_1', '#skF_3'), '#skF_1', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_4152])).
% 6.87/2.44  tff(c_4161, plain, (v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_3163, c_4157])).
% 6.87/2.44  tff(c_5215, plain, (![A_469, B_470]: (m1_subset_1(k2_funct_2(A_469, B_470), k1_zfmisc_1(k2_zfmisc_1(A_469, A_469))) | ~m1_subset_1(B_470, k1_zfmisc_1(k2_zfmisc_1(A_469, A_469))) | ~v3_funct_2(B_470, A_469, A_469) | ~v1_funct_2(B_470, A_469, A_469) | ~v1_funct_1(B_470))), inference(cnfTransformation, [status(thm)], [f_140])).
% 6.87/2.44  tff(c_5250, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3163, c_5215])).
% 6.87/2.44  tff(c_5266, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_64, c_62, c_5250])).
% 6.87/2.44  tff(c_38, plain, (![C_36, B_35, A_34]: (v2_funct_2(C_36, B_35) | ~v3_funct_2(C_36, A_34, B_35) | ~v1_funct_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.87/2.44  tff(c_5279, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v3_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5266, c_38])).
% 6.87/2.44  tff(c_5313, plain, (v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3164, c_4161, c_5279])).
% 6.87/2.44  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.87/2.44  tff(c_5295, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_5266, c_12])).
% 6.87/2.44  tff(c_5323, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_5295])).
% 6.87/2.44  tff(c_30, plain, (![C_25, B_24, A_23]: (v5_relat_1(C_25, B_24) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.87/2.44  tff(c_5319, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_5266, c_30])).
% 6.87/2.44  tff(c_46, plain, (![B_38, A_37]: (k2_relat_1(B_38)=A_37 | ~v2_funct_2(B_38, A_37) | ~v5_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.87/2.44  tff(c_5327, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5319, c_46])).
% 6.87/2.44  tff(c_5330, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v2_funct_2(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5323, c_5327])).
% 6.87/2.44  tff(c_5791, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5313, c_5330])).
% 6.87/2.44  tff(c_32, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.87/2.44  tff(c_5320, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_5266, c_32])).
% 6.87/2.44  tff(c_20, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.87/2.44  tff(c_5333, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_5320, c_20])).
% 6.87/2.44  tff(c_5336, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5323, c_5333])).
% 6.87/2.44  tff(c_5380, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5336, c_16])).
% 6.87/2.44  tff(c_5386, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5323, c_5380])).
% 6.87/2.44  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.44  tff(c_1637, plain, (![B_320, A_321]: (k9_relat_1(B_320, k10_relat_1(B_320, A_321))=A_321 | ~r1_tarski(A_321, k2_relat_1(B_320)) | ~v1_funct_1(B_320) | ~v1_relat_1(B_320))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.87/2.44  tff(c_1644, plain, (![A_321]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_321))=A_321 | ~r1_tarski(A_321, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1405, c_1637])).
% 6.87/2.44  tff(c_1655, plain, (![A_322]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_322))=A_322 | ~r1_tarski(A_322, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_68, c_1644])).
% 6.87/2.44  tff(c_1680, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1655])).
% 6.87/2.44  tff(c_1700, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1680])).
% 6.87/2.44  tff(c_1441, plain, (![B_289, A_290]: (r1_tarski(k9_relat_1(B_289, k10_relat_1(B_289, A_290)), A_290) | ~v1_funct_1(B_289) | ~v1_relat_1(B_289))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.87/2.44  tff(c_1457, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1420, c_1441])).
% 6.87/2.44  tff(c_1466, plain, (r1_tarski(k9_relat_1('#skF_3', k1_relat_1('#skF_3')), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_68, c_1457])).
% 6.87/2.44  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.87/2.44  tff(c_1472, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(resolution, [status(thm)], [c_1466, c_2])).
% 6.87/2.44  tff(c_1494, plain, (~r1_tarski('#skF_1', k9_relat_1('#skF_3', k1_relat_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1472])).
% 6.87/2.44  tff(c_1703, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1700, c_1494])).
% 6.87/2.44  tff(c_1707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1703])).
% 6.87/2.44  tff(c_1708, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_1472])).
% 6.87/2.44  tff(c_1474, plain, (![B_291, A_292]: (k10_relat_1(k2_funct_1(B_291), A_292)=k9_relat_1(B_291, A_292) | ~v2_funct_1(B_291) | ~v1_funct_1(B_291) | ~v1_relat_1(B_291))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.87/2.44  tff(c_22, plain, (![B_16, A_15]: (r1_tarski(k9_relat_1(B_16, k10_relat_1(B_16, A_15)), A_15) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.87/2.44  tff(c_5499, plain, (![B_474, A_475]: (r1_tarski(k9_relat_1(k2_funct_1(B_474), k9_relat_1(B_474, A_475)), A_475) | ~v1_funct_1(k2_funct_1(B_474)) | ~v1_relat_1(k2_funct_1(B_474)) | ~v2_funct_1(B_474) | ~v1_funct_1(B_474) | ~v1_relat_1(B_474))), inference(superposition, [status(thm), theory('equality')], [c_1474, c_22])).
% 6.87/2.44  tff(c_5572, plain, (r1_tarski(k9_relat_1(k2_funct_1('#skF_3'), '#skF_1'), k1_relat_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1708, c_5499])).
% 6.87/2.44  tff(c_5603, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_68, c_1916, c_5323, c_3164, c_5386, c_5572])).
% 6.87/2.44  tff(c_5793, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5791, c_5603])).
% 6.87/2.44  tff(c_28, plain, (![B_22, A_21]: (k10_relat_1(B_22, k9_relat_1(B_22, A_21))=A_21 | ~v2_funct_1(B_22) | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.87/2.44  tff(c_5869, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_5793, c_28])).
% 6.87/2.44  tff(c_5877, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_68, c_1916, c_1420, c_1407, c_5869])).
% 6.87/2.44  tff(c_5948, plain, (![A_21]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_21))=A_21 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_21, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5877, c_28])).
% 6.87/2.44  tff(c_6674, plain, (![A_494]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_494))=A_494 | ~r1_tarski(A_494, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1000, c_68, c_1916, c_5948])).
% 6.87/2.44  tff(c_1953, plain, (![A_349, B_350, C_351, D_352]: (k7_relset_1(A_349, B_350, C_351, D_352)=k9_relat_1(C_351, D_352) | ~m1_subset_1(C_351, k1_zfmisc_1(k2_zfmisc_1(A_349, B_350))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.87/2.44  tff(c_1960, plain, (![D_352]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_352)=k9_relat_1('#skF_3', D_352))), inference(resolution, [status(thm)], [c_62, c_1953])).
% 6.87/2.44  tff(c_1934, plain, (![A_344, B_345, C_346, D_347]: (k8_relset_1(A_344, B_345, C_346, D_347)=k10_relat_1(C_346, D_347) | ~m1_subset_1(C_346, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.87/2.44  tff(c_1941, plain, (![D_347]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_347)=k10_relat_1('#skF_3', D_347))), inference(resolution, [status(thm)], [c_62, c_1934])).
% 6.87/2.44  tff(c_83, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.87/2.44  tff(c_89, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_62, c_83])).
% 6.87/2.44  tff(c_93, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_89])).
% 6.87/2.44  tff(c_133, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.87/2.44  tff(c_142, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_62, c_133])).
% 6.87/2.44  tff(c_243, plain, (![B_82, A_83]: (k2_relat_1(B_82)=A_83 | ~v2_funct_2(B_82, A_83) | ~v5_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_124])).
% 6.87/2.44  tff(c_249, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_142, c_243])).
% 6.87/2.44  tff(c_255, plain, (k2_relat_1('#skF_3')='#skF_1' | ~v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_93, c_249])).
% 6.87/2.44  tff(c_256, plain, (~v2_funct_2('#skF_3', '#skF_1')), inference(splitLeft, [status(thm)], [c_255])).
% 6.87/2.44  tff(c_501, plain, (![C_134, B_135, A_136]: (v2_funct_2(C_134, B_135) | ~v3_funct_2(C_134, A_136, B_135) | ~v1_funct_1(C_134) | ~m1_subset_1(C_134, k1_zfmisc_1(k2_zfmisc_1(A_136, B_135))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.87/2.44  tff(c_508, plain, (v2_funct_2('#skF_3', '#skF_1') | ~v3_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_62, c_501])).
% 6.87/2.44  tff(c_512, plain, (v2_funct_2('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_64, c_508])).
% 6.87/2.44  tff(c_514, plain, $false, inference(negUnitSimplification, [status(thm)], [c_256, c_512])).
% 6.87/2.44  tff(c_515, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_255])).
% 6.87/2.44  tff(c_934, plain, (![B_203, A_204]: (k9_relat_1(B_203, k10_relat_1(B_203, A_204))=A_204 | ~r1_tarski(A_204, k2_relat_1(B_203)) | ~v1_funct_1(B_203) | ~v1_relat_1(B_203))), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.87/2.44  tff(c_941, plain, (![A_204]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_204))=A_204 | ~r1_tarski(A_204, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_934])).
% 6.87/2.44  tff(c_952, plain, (![A_205]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_205))=A_205 | ~r1_tarski(A_205, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_93, c_68, c_941])).
% 6.87/2.44  tff(c_903, plain, (![A_194, B_195, C_196, D_197]: (k8_relset_1(A_194, B_195, C_196, D_197)=k10_relat_1(C_196, D_197) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_194, B_195))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.87/2.44  tff(c_910, plain, (![D_197]: (k8_relset_1('#skF_1', '#skF_1', '#skF_3', D_197)=k10_relat_1('#skF_3', D_197))), inference(resolution, [status(thm)], [c_62, c_903])).
% 6.87/2.44  tff(c_885, plain, (![A_189, B_190, C_191, D_192]: (k7_relset_1(A_189, B_190, C_191, D_192)=k9_relat_1(C_191, D_192) | ~m1_subset_1(C_191, k1_zfmisc_1(k2_zfmisc_1(A_189, B_190))))), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.87/2.44  tff(c_892, plain, (![D_192]: (k7_relset_1('#skF_1', '#skF_1', '#skF_3', D_192)=k9_relat_1('#skF_3', D_192))), inference(resolution, [status(thm)], [c_62, c_885])).
% 6.87/2.44  tff(c_58, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2' | k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_165])).
% 6.87/2.44  tff(c_82, plain, (k7_relset_1('#skF_1', '#skF_1', '#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 6.87/2.44  tff(c_893, plain, (k9_relat_1('#skF_3', k8_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_892, c_82])).
% 6.87/2.44  tff(c_920, plain, (k9_relat_1('#skF_3', k10_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_910, c_893])).
% 6.87/2.44  tff(c_958, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_952, c_920])).
% 6.87/2.44  tff(c_987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_958])).
% 6.87/2.44  tff(c_988, plain, (k8_relset_1('#skF_1', '#skF_1', '#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 6.87/2.44  tff(c_1942, plain, (k10_relat_1('#skF_3', k7_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1941, c_988])).
% 6.87/2.44  tff(c_1965, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1960, c_1942])).
% 6.87/2.44  tff(c_6696, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6674, c_1965])).
% 6.87/2.44  tff(c_6752, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_6696])).
% 6.87/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.87/2.44  
% 6.87/2.44  Inference rules
% 6.87/2.44  ----------------------
% 6.87/2.44  #Ref     : 0
% 6.87/2.44  #Sup     : 1455
% 6.87/2.44  #Fact    : 0
% 6.87/2.44  #Define  : 0
% 6.87/2.44  #Split   : 29
% 6.87/2.44  #Chain   : 0
% 6.87/2.44  #Close   : 0
% 6.87/2.44  
% 6.87/2.44  Ordering : KBO
% 6.87/2.44  
% 6.87/2.44  Simplification rules
% 6.87/2.44  ----------------------
% 6.87/2.44  #Subsume      : 94
% 6.87/2.44  #Demod        : 2214
% 6.87/2.44  #Tautology    : 587
% 6.87/2.44  #SimpNegUnit  : 18
% 6.87/2.44  #BackRed      : 77
% 6.87/2.44  
% 6.87/2.44  #Partial instantiations: 0
% 6.87/2.44  #Strategies tried      : 1
% 6.87/2.44  
% 6.87/2.44  Timing (in seconds)
% 6.87/2.44  ----------------------
% 6.87/2.44  Preprocessing        : 0.35
% 6.87/2.44  Parsing              : 0.19
% 6.87/2.44  CNF conversion       : 0.02
% 6.87/2.44  Main loop            : 1.30
% 6.87/2.44  Inferencing          : 0.44
% 6.87/2.44  Reduction            : 0.49
% 6.87/2.44  Demodulation         : 0.36
% 6.87/2.44  BG Simplification    : 0.05
% 6.87/2.44  Subsumption          : 0.21
% 6.87/2.44  Abstraction          : 0.06
% 6.87/2.44  MUC search           : 0.00
% 6.87/2.44  Cooper               : 0.00
% 6.87/2.44  Total                : 1.71
% 6.87/2.44  Index Insertion      : 0.00
% 6.87/2.44  Index Deletion       : 0.00
% 6.87/2.45  Index Matching       : 0.00
% 6.87/2.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
