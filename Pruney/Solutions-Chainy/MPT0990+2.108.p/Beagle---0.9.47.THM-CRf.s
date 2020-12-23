%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:11 EST 2020

% Result     : Theorem 13.57s
% Output     : CNFRefutation 13.70s
% Verified   : 
% Statistics : Number of formulae       :  223 (3338 expanded)
%              Number of leaves         :   58 (1189 expanded)
%              Depth                    :   29
%              Number of atoms          :  464 (10755 expanded)
%              Number of equality atoms :  138 (3086 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_228,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

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

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_192,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_85,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_146,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_152,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_107,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_176,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_180,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_164,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_190,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_89,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_95,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_202,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_136,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_115,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(A,k2_relat_1(B))
       => k9_relat_1(B,k10_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_funct_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(c_84,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_96,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_208,plain,(
    ! [B_83,A_84] :
      ( v1_relat_1(B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_84))
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_214,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_96,c_208])).

tff(c_223,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_214])).

tff(c_102,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_217,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_208])).

tff(c_226,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_217])).

tff(c_106,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_38,plain,(
    ! [A_30] :
      ( v1_relat_1(k2_funct_1(A_30))
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_90,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_76,plain,(
    ! [A_62] : k6_relat_1(A_62) = k6_partfun1(A_62) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_28,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_114,plain,(
    ! [A_26] : k1_relat_1(k6_partfun1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_28])).

tff(c_94,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_909,plain,(
    ! [A_136,B_137,C_138] :
      ( k2_relset_1(A_136,B_137,C_138) = k2_relat_1(C_138)
      | ~ m1_subset_1(C_138,k1_zfmisc_1(k2_zfmisc_1(A_136,B_137))) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_921,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_909])).

tff(c_927,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_921])).

tff(c_52,plain,(
    ! [A_38] :
      ( k5_relat_1(k2_funct_1(A_38),A_38) = k6_relat_1(k2_relat_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_108,plain,(
    ! [A_38] :
      ( k5_relat_1(k2_funct_1(A_38),A_38) = k6_partfun1(k2_relat_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_52])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_274,plain,(
    ! [C_95,A_96,B_97] :
      ( v4_relat_1(C_95,A_96)
      | ~ m1_subset_1(C_95,k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_286,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_102,c_274])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_40,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_110,plain,(
    ! [A_31] : v1_relat_1(k6_partfun1(A_31)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_40])).

tff(c_100,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_11561,plain,(
    ! [A_420,C_416,D_421,B_418,F_419,E_417] :
      ( m1_subset_1(k1_partfun1(A_420,B_418,C_416,D_421,E_417,F_419),k1_zfmisc_1(k2_zfmisc_1(A_420,D_421)))
      | ~ m1_subset_1(F_419,k1_zfmisc_1(k2_zfmisc_1(C_416,D_421)))
      | ~ v1_funct_1(F_419)
      | ~ m1_subset_1(E_417,k1_zfmisc_1(k2_zfmisc_1(A_420,B_418)))
      | ~ v1_funct_1(E_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_72,plain,(
    ! [A_55] : m1_subset_1(k6_partfun1(A_55),k1_zfmisc_1(k2_zfmisc_1(A_55,A_55))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_92,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_228])).

tff(c_11222,plain,(
    ! [D_390,C_391,A_392,B_393] :
      ( D_390 = C_391
      | ~ r2_relset_1(A_392,B_393,C_391,D_390)
      | ~ m1_subset_1(D_390,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393)))
      | ~ m1_subset_1(C_391,k1_zfmisc_1(k2_zfmisc_1(A_392,B_393))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_11234,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_92,c_11222])).

tff(c_11255,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_11234])).

tff(c_11360,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_11255])).

tff(c_11569,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11561,c_11360])).

tff(c_11594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_100,c_96,c_11569])).

tff(c_11595,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_11255])).

tff(c_11753,plain,(
    ! [C_436,B_434,F_435,E_437,A_439,D_438] :
      ( k1_partfun1(A_439,B_434,C_436,D_438,E_437,F_435) = k5_relat_1(E_437,F_435)
      | ~ m1_subset_1(F_435,k1_zfmisc_1(k2_zfmisc_1(C_436,D_438)))
      | ~ v1_funct_1(F_435)
      | ~ m1_subset_1(E_437,k1_zfmisc_1(k2_zfmisc_1(A_439,B_434)))
      | ~ v1_funct_1(E_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_11761,plain,(
    ! [A_439,B_434,E_437] :
      ( k1_partfun1(A_439,B_434,'#skF_2','#skF_1',E_437,'#skF_4') = k5_relat_1(E_437,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_437,k1_zfmisc_1(k2_zfmisc_1(A_439,B_434)))
      | ~ v1_funct_1(E_437) ) ),
    inference(resolution,[status(thm)],[c_96,c_11753])).

tff(c_11951,plain,(
    ! [A_449,B_450,E_451] :
      ( k1_partfun1(A_449,B_450,'#skF_2','#skF_1',E_451,'#skF_4') = k5_relat_1(E_451,'#skF_4')
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ v1_funct_1(E_451) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_11761])).

tff(c_11966,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_11951])).

tff(c_11977,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_11595,c_11966])).

tff(c_32,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_112,plain,(
    ! [A_27] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_27)),A_27) = A_27
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_1526,plain,(
    ! [A_160,B_161,C_162] :
      ( k5_relat_1(k5_relat_1(A_160,B_161),C_162) = k5_relat_1(A_160,k5_relat_1(B_161,C_162))
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(B_161)
      | ~ v1_relat_1(A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1582,plain,(
    ! [A_27,C_162] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_27)),k5_relat_1(A_27,C_162)) = k5_relat_1(A_27,C_162)
      | ~ v1_relat_1(C_162)
      | ~ v1_relat_1(A_27)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_27)))
      | ~ v1_relat_1(A_27) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_1526])).

tff(c_12457,plain,(
    ! [A_464,C_465] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_464)),k5_relat_1(A_464,C_465)) = k5_relat_1(A_464,C_465)
      | ~ v1_relat_1(C_465)
      | ~ v1_relat_1(A_464) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1582])).

tff(c_12493,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11977,c_12457])).

tff(c_12563,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1('#skF_1')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_223,c_11977,c_12493])).

tff(c_22,plain,(
    ! [A_14,B_16] :
      ( k10_relat_1(A_14,k1_relat_1(B_16)) = k1_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_30,plain,(
    ! [A_26] : k2_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_113,plain,(
    ! [A_26] : k2_relat_1(k6_partfun1(A_26)) = A_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_30])).

tff(c_34,plain,(
    ! [B_29,A_28] :
      ( k5_relat_1(B_29,k6_relat_1(A_28)) = B_29
      | ~ r1_tarski(k2_relat_1(B_29),A_28)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_555,plain,(
    ! [B_121,A_122] :
      ( k5_relat_1(B_121,k6_partfun1(A_122)) = B_121
      | ~ r1_tarski(k2_relat_1(B_121),A_122)
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_34])).

tff(c_561,plain,(
    ! [A_26,A_122] :
      ( k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_122)) = k6_partfun1(A_26)
      | ~ r1_tarski(A_26,A_122)
      | ~ v1_relat_1(k6_partfun1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_555])).

tff(c_567,plain,(
    ! [A_26,A_122] :
      ( k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_122)) = k6_partfun1(A_26)
      | ~ r1_tarski(A_26,A_122) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_561])).

tff(c_655,plain,(
    ! [A_127,B_128] :
      ( k10_relat_1(A_127,k1_relat_1(B_128)) = k1_relat_1(k5_relat_1(A_127,B_128))
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_675,plain,(
    ! [A_127,A_26] :
      ( k1_relat_1(k5_relat_1(A_127,k6_partfun1(A_26))) = k10_relat_1(A_127,A_26)
      | ~ v1_relat_1(k6_partfun1(A_26))
      | ~ v1_relat_1(A_127) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_655])).

tff(c_733,plain,(
    ! [A_131,A_132] :
      ( k1_relat_1(k5_relat_1(A_131,k6_partfun1(A_132))) = k10_relat_1(A_131,A_132)
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_675])).

tff(c_769,plain,(
    ! [A_26,A_122] :
      ( k10_relat_1(k6_partfun1(A_26),A_122) = k1_relat_1(k6_partfun1(A_26))
      | ~ v1_relat_1(k6_partfun1(A_26))
      | ~ r1_tarski(A_26,A_122) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_567,c_733])).

tff(c_788,plain,(
    ! [A_133,A_134] :
      ( k10_relat_1(k6_partfun1(A_133),A_134) = A_133
      | ~ r1_tarski(A_133,A_134) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_114,c_769])).

tff(c_810,plain,(
    ! [A_133,B_16] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_133),B_16)) = A_133
      | ~ r1_tarski(A_133,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(k6_partfun1(A_133)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_788])).

tff(c_828,plain,(
    ! [A_133,B_16] :
      ( k1_relat_1(k5_relat_1(k6_partfun1(A_133),B_16)) = A_133
      | ~ r1_tarski(A_133,k1_relat_1(B_16))
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_810])).

tff(c_12773,plain,
    ( k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(k6_partfun1('#skF_1')))
    | ~ v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_12563,c_828])).

tff(c_12795,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_114,c_114,c_12773])).

tff(c_12812,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_12795])).

tff(c_12825,plain,
    ( ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_12812])).

tff(c_12829,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_286,c_12825])).

tff(c_12830,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_12795])).

tff(c_78,plain,(
    ! [A_63] :
      ( m1_subset_1(A_63,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_63),k2_relat_1(A_63))))
      | ~ v1_funct_1(A_63)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_202])).

tff(c_935,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_78])).

tff(c_953,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_935])).

tff(c_58,plain,(
    ! [C_41,A_39,B_40] :
      ( v4_relat_1(C_41,A_39)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_1010,plain,(
    v4_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_953,c_58])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1018,plain,
    ( k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1010,c_24])).

tff(c_1021,plain,(
    k7_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_1018])).

tff(c_18,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1037,plain,
    ( k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1021,c_18])).

tff(c_1047,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_927,c_1037])).

tff(c_10981,plain,(
    ! [A_383,B_384] :
      ( k9_relat_1(k2_funct_1(A_383),k9_relat_1(A_383,B_384)) = B_384
      | ~ r1_tarski(B_384,k1_relat_1(A_383))
      | ~ v2_funct_1(A_383)
      | ~ v1_funct_1(A_383)
      | ~ v1_relat_1(A_383) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_11008,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1047,c_10981])).

tff(c_11033,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_6,c_11008])).

tff(c_293,plain,(
    ! [B_99,A_100] :
      ( k7_relat_1(B_99,A_100) = B_99
      | ~ v4_relat_1(B_99,A_100)
      | ~ v1_relat_1(B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_299,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_286,c_293])).

tff(c_308,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_299])).

tff(c_316,plain,(
    ! [B_101,A_102] :
      ( k2_relat_1(k7_relat_1(B_101,A_102)) = k9_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_328,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_316])).

tff(c_332,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_328])).

tff(c_928,plain,(
    k9_relat_1('#skF_3','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_332])).

tff(c_11011,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_10981])).

tff(c_11035,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_11011])).

tff(c_11220,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11033,c_11035])).

tff(c_11221,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11220])).

tff(c_12839,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12830,c_11221])).

tff(c_12856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_12839])).

tff(c_12857,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_11220])).

tff(c_12894,plain,(
    ! [A_14] :
      ( k1_relat_1(k5_relat_1(A_14,'#skF_3')) = k10_relat_1(A_14,'#skF_1')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12857,c_22])).

tff(c_13976,plain,(
    ! [A_528] :
      ( k1_relat_1(k5_relat_1(A_528,'#skF_3')) = k10_relat_1(A_528,'#skF_1')
      | ~ v1_relat_1(A_528) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_12894])).

tff(c_14048,plain,
    ( k1_relat_1(k6_partfun1(k2_relat_1('#skF_3'))) = k10_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_13976])).

tff(c_14072,plain,
    ( k10_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_2'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_114,c_927,c_14048])).

tff(c_14077,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_14072])).

tff(c_14101,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_14077])).

tff(c_14105,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_14101])).

tff(c_14107,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_14072])).

tff(c_12859,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12857,c_11033])).

tff(c_50,plain,(
    ! [A_37] :
      ( k1_relat_1(k2_funct_1(A_37)) = k2_relat_1(A_37)
      | ~ v2_funct_1(A_37)
      | ~ v1_funct_1(A_37)
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_185,plain,(
    ! [A_81] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_81)),A_81) = A_81
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_32])).

tff(c_194,plain,(
    ! [A_26] :
      ( k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_26)) = k6_partfun1(A_26)
      | ~ v1_relat_1(k6_partfun1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_185])).

tff(c_198,plain,(
    ! [A_26] : k5_relat_1(k6_partfun1(A_26),k6_partfun1(A_26)) = k6_partfun1(A_26) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_194])).

tff(c_54,plain,(
    ! [A_38] :
      ( k5_relat_1(A_38,k2_funct_1(A_38)) = k6_relat_1(k1_relat_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_107,plain,(
    ! [A_38] :
      ( k5_relat_1(A_38,k2_funct_1(A_38)) = k6_partfun1(k1_relat_1(A_38))
      | ~ v2_funct_1(A_38)
      | ~ v1_funct_1(A_38)
      | ~ v1_relat_1(A_38) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_54])).

tff(c_12915,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12857,c_112])).

tff(c_12943,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_12915])).

tff(c_26,plain,(
    ! [A_19,B_23,C_25] :
      ( k5_relat_1(k5_relat_1(A_19,B_23),C_25) = k5_relat_1(A_19,k5_relat_1(B_23,C_25))
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1(B_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_12999,plain,(
    ! [C_25] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_25)) = k5_relat_1('#skF_3',C_25)
      | ~ v1_relat_1(C_25)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12943,c_26])).

tff(c_14182,plain,(
    ! [C_541] :
      ( k5_relat_1(k6_partfun1('#skF_1'),k5_relat_1('#skF_3',C_541)) = k5_relat_1('#skF_3',C_541)
      | ~ v1_relat_1(C_541) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_226,c_12999])).

tff(c_14213,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_14182])).

tff(c_14230,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_14107,c_198,c_12857,c_14213])).

tff(c_1348,plain,(
    ! [B_152,A_153] :
      ( k9_relat_1(B_152,k10_relat_1(B_152,A_153)) = A_153
      | ~ r1_tarski(A_153,k2_relat_1(B_152))
      | ~ v1_funct_1(B_152)
      | ~ v1_relat_1(B_152) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_1350,plain,(
    ! [A_153] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_153)) = A_153
      | ~ r1_tarski(A_153,'#skF_2')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_1348])).

tff(c_1369,plain,(
    ! [A_154] :
      ( k9_relat_1('#skF_3',k10_relat_1('#skF_3',A_154)) = A_154
      | ~ r1_tarski(A_154,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_1350])).

tff(c_1382,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_16))) = k1_relat_1(B_16)
      | ~ r1_tarski(k1_relat_1(B_16),'#skF_2')
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1369])).

tff(c_1392,plain,(
    ! [B_16] :
      ( k9_relat_1('#skF_3',k1_relat_1(k5_relat_1('#skF_3',B_16))) = k1_relat_1(B_16)
      | ~ r1_tarski(k1_relat_1(B_16),'#skF_2')
      | ~ v1_relat_1(B_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_1382])).

tff(c_14242,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1(k2_funct_1('#skF_3'))
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14230,c_1392])).

tff(c_14257,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2'
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_928,c_114,c_14242])).

tff(c_14265,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_14257])).

tff(c_14268,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_14265])).

tff(c_14274,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_6,c_927,c_14268])).

tff(c_14275,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_14257])).

tff(c_16,plain,(
    ! [A_10] :
      ( k9_relat_1(A_10,k1_relat_1(A_10)) = k2_relat_1(A_10)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14341,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14275,c_16])).

tff(c_14375,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_12859,c_14341])).

tff(c_568,plain,(
    ! [B_121] :
      ( k5_relat_1(B_121,k6_partfun1(k2_relat_1(B_121))) = B_121
      | ~ v1_relat_1(B_121) ) ),
    inference(resolution,[status(thm)],[c_6,c_555])).

tff(c_14407,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_14375,c_568])).

tff(c_14438,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14107,c_14407])).

tff(c_285,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_96,c_274])).

tff(c_66,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] :
      ( m1_subset_1(k1_partfun1(A_49,B_50,C_51,D_52,E_53,F_54),k1_zfmisc_1(k2_zfmisc_1(A_49,D_52)))
      | ~ m1_subset_1(F_54,k1_zfmisc_1(k2_zfmisc_1(C_51,D_52)))
      | ~ v1_funct_1(F_54)
      | ~ m1_subset_1(E_53,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(E_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_12946,plain,(
    ! [D_470,C_471,A_472,B_473] :
      ( D_470 = C_471
      | ~ r2_relset_1(A_472,B_473,C_471,D_470)
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473)))
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473))) ) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_12956,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_92,c_12946])).

tff(c_12973,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_12956])).

tff(c_13015,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_12973])).

tff(c_13617,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_13015])).

tff(c_13621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_102,c_100,c_96,c_13617])).

tff(c_13622,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_12973])).

tff(c_13958,plain,(
    ! [C_524,E_525,B_522,A_527,D_526,F_523] :
      ( k1_partfun1(A_527,B_522,C_524,D_526,E_525,F_523) = k5_relat_1(E_525,F_523)
      | ~ m1_subset_1(F_523,k1_zfmisc_1(k2_zfmisc_1(C_524,D_526)))
      | ~ v1_funct_1(F_523)
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(A_527,B_522)))
      | ~ v1_funct_1(E_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_13964,plain,(
    ! [A_527,B_522,E_525] :
      ( k1_partfun1(A_527,B_522,'#skF_2','#skF_1',E_525,'#skF_4') = k5_relat_1(E_525,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_525,k1_zfmisc_1(k2_zfmisc_1(A_527,B_522)))
      | ~ v1_funct_1(E_525) ) ),
    inference(resolution,[status(thm)],[c_96,c_13958])).

tff(c_14961,plain,(
    ! [A_551,B_552,E_553] :
      ( k1_partfun1(A_551,B_552,'#skF_2','#skF_1',E_553,'#skF_4') = k5_relat_1(E_553,'#skF_4')
      | ~ m1_subset_1(E_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552)))
      | ~ v1_funct_1(E_553) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_13964])).

tff(c_14982,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_14961])).

tff(c_14997,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_13622,c_14982])).

tff(c_15007,plain,
    ( k9_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14997,c_1392])).

tff(c_15018,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_928,c_114,c_15007])).

tff(c_15022,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_15018])).

tff(c_15025,plain,
    ( ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_15022])).

tff(c_15029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_285,c_15025])).

tff(c_15030,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_15018])).

tff(c_15077,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15030,c_112])).

tff(c_15109,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_15077])).

tff(c_21799,plain,(
    ! [A_666,C_667] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_666)),C_667) = k5_relat_1(k2_funct_1(A_666),k5_relat_1(A_666,C_667))
      | ~ v1_relat_1(C_667)
      | ~ v1_relat_1(A_666)
      | ~ v1_relat_1(k2_funct_1(A_666))
      | ~ v2_funct_1(A_666)
      | ~ v1_funct_1(A_666)
      | ~ v1_relat_1(A_666) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_1526])).

tff(c_21991,plain,(
    ! [C_667] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_667)) = k5_relat_1(k6_partfun1('#skF_2'),C_667)
      | ~ v1_relat_1(C_667)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_927,c_21799])).

tff(c_28144,plain,(
    ! [C_798] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_798)) = k5_relat_1(k6_partfun1('#skF_2'),C_798)
      | ~ v1_relat_1(C_798) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_106,c_90,c_14107,c_226,c_21991])).

tff(c_28202,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_14997,c_28144])).

tff(c_28256,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_14438,c_15109,c_28202])).

tff(c_28258,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_28256])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:03:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.57/6.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.61/6.54  
% 13.61/6.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/6.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 13.70/6.54  
% 13.70/6.54  %Foreground sorts:
% 13.70/6.54  
% 13.70/6.54  
% 13.70/6.54  %Background operators:
% 13.70/6.54  
% 13.70/6.54  
% 13.70/6.54  %Foreground operators:
% 13.70/6.54  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 13.70/6.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 13.70/6.54  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 13.70/6.54  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 13.70/6.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.70/6.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 13.70/6.54  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 13.70/6.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.70/6.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 13.70/6.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.70/6.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 13.70/6.54  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.70/6.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 13.70/6.54  tff('#skF_2', type, '#skF_2': $i).
% 13.70/6.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 13.70/6.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 13.70/6.54  tff('#skF_3', type, '#skF_3': $i).
% 13.70/6.54  tff('#skF_1', type, '#skF_1': $i).
% 13.70/6.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 13.70/6.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.70/6.54  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 13.70/6.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.70/6.54  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.70/6.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.70/6.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 13.70/6.54  tff('#skF_4', type, '#skF_4': $i).
% 13.70/6.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 13.70/6.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.70/6.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 13.70/6.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.70/6.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.70/6.54  
% 13.70/6.57  tff(f_228, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 13.70/6.57  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 13.70/6.57  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.70/6.57  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 13.70/6.57  tff(f_192, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 13.70/6.57  tff(f_85, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 13.70/6.57  tff(f_156, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 13.70/6.57  tff(f_146, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 13.70/6.57  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.70/6.57  tff(f_152, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 13.70/6.57  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 13.70/6.57  tff(f_107, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 13.70/6.57  tff(f_176, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 13.70/6.57  tff(f_180, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 13.70/6.57  tff(f_164, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 13.70/6.57  tff(f_190, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 13.70/6.57  tff(f_89, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 13.70/6.57  tff(f_81, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 13.70/6.57  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 13.70/6.57  tff(f_95, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 13.70/6.57  tff(f_202, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 13.70/6.57  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 13.70/6.57  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 13.70/6.57  tff(f_126, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 13.70/6.57  tff(f_136, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 13.70/6.57  tff(f_115, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(A, k2_relat_1(B)) => (k9_relat_1(B, k10_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_funct_1)).
% 13.70/6.57  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 13.70/6.57  tff(c_84, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 13.70/6.57  tff(c_96, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_208, plain, (![B_83, A_84]: (v1_relat_1(B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_84)) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_38])).
% 13.70/6.57  tff(c_214, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_96, c_208])).
% 13.70/6.57  tff(c_223, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_214])).
% 13.70/6.57  tff(c_102, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_217, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_102, c_208])).
% 13.70/6.57  tff(c_226, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_217])).
% 13.70/6.57  tff(c_106, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_38, plain, (![A_30]: (v1_relat_1(k2_funct_1(A_30)) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_103])).
% 13.70/6.57  tff(c_90, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_76, plain, (![A_62]: (k6_relat_1(A_62)=k6_partfun1(A_62))), inference(cnfTransformation, [status(thm)], [f_192])).
% 13.70/6.57  tff(c_28, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.70/6.57  tff(c_114, plain, (![A_26]: (k1_relat_1(k6_partfun1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_28])).
% 13.70/6.57  tff(c_94, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_909, plain, (![A_136, B_137, C_138]: (k2_relset_1(A_136, B_137, C_138)=k2_relat_1(C_138) | ~m1_subset_1(C_138, k1_zfmisc_1(k2_zfmisc_1(A_136, B_137))))), inference(cnfTransformation, [status(thm)], [f_156])).
% 13.70/6.57  tff(c_921, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_909])).
% 13.70/6.57  tff(c_927, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_921])).
% 13.70/6.57  tff(c_52, plain, (![A_38]: (k5_relat_1(k2_funct_1(A_38), A_38)=k6_relat_1(k2_relat_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.70/6.57  tff(c_108, plain, (![A_38]: (k5_relat_1(k2_funct_1(A_38), A_38)=k6_partfun1(k2_relat_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_52])).
% 13.70/6.57  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.70/6.57  tff(c_274, plain, (![C_95, A_96, B_97]: (v4_relat_1(C_95, A_96) | ~m1_subset_1(C_95, k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.70/6.57  tff(c_286, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_102, c_274])).
% 13.70/6.57  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 13.70/6.57  tff(c_40, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_107])).
% 13.70/6.57  tff(c_110, plain, (![A_31]: (v1_relat_1(k6_partfun1(A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_40])).
% 13.70/6.57  tff(c_100, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_11561, plain, (![A_420, C_416, D_421, B_418, F_419, E_417]: (m1_subset_1(k1_partfun1(A_420, B_418, C_416, D_421, E_417, F_419), k1_zfmisc_1(k2_zfmisc_1(A_420, D_421))) | ~m1_subset_1(F_419, k1_zfmisc_1(k2_zfmisc_1(C_416, D_421))) | ~v1_funct_1(F_419) | ~m1_subset_1(E_417, k1_zfmisc_1(k2_zfmisc_1(A_420, B_418))) | ~v1_funct_1(E_417))), inference(cnfTransformation, [status(thm)], [f_176])).
% 13.70/6.57  tff(c_72, plain, (![A_55]: (m1_subset_1(k6_partfun1(A_55), k1_zfmisc_1(k2_zfmisc_1(A_55, A_55))))), inference(cnfTransformation, [status(thm)], [f_180])).
% 13.70/6.57  tff(c_92, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_228])).
% 13.70/6.57  tff(c_11222, plain, (![D_390, C_391, A_392, B_393]: (D_390=C_391 | ~r2_relset_1(A_392, B_393, C_391, D_390) | ~m1_subset_1(D_390, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))) | ~m1_subset_1(C_391, k1_zfmisc_1(k2_zfmisc_1(A_392, B_393))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.70/6.57  tff(c_11234, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_92, c_11222])).
% 13.70/6.57  tff(c_11255, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_11234])).
% 13.70/6.57  tff(c_11360, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_11255])).
% 13.70/6.57  tff(c_11569, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_11561, c_11360])).
% 13.70/6.57  tff(c_11594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_100, c_96, c_11569])).
% 13.70/6.57  tff(c_11595, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_11255])).
% 13.70/6.57  tff(c_11753, plain, (![C_436, B_434, F_435, E_437, A_439, D_438]: (k1_partfun1(A_439, B_434, C_436, D_438, E_437, F_435)=k5_relat_1(E_437, F_435) | ~m1_subset_1(F_435, k1_zfmisc_1(k2_zfmisc_1(C_436, D_438))) | ~v1_funct_1(F_435) | ~m1_subset_1(E_437, k1_zfmisc_1(k2_zfmisc_1(A_439, B_434))) | ~v1_funct_1(E_437))), inference(cnfTransformation, [status(thm)], [f_190])).
% 13.70/6.57  tff(c_11761, plain, (![A_439, B_434, E_437]: (k1_partfun1(A_439, B_434, '#skF_2', '#skF_1', E_437, '#skF_4')=k5_relat_1(E_437, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_437, k1_zfmisc_1(k2_zfmisc_1(A_439, B_434))) | ~v1_funct_1(E_437))), inference(resolution, [status(thm)], [c_96, c_11753])).
% 13.70/6.57  tff(c_11951, plain, (![A_449, B_450, E_451]: (k1_partfun1(A_449, B_450, '#skF_2', '#skF_1', E_451, '#skF_4')=k5_relat_1(E_451, '#skF_4') | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~v1_funct_1(E_451))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_11761])).
% 13.70/6.57  tff(c_11966, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_11951])).
% 13.70/6.57  tff(c_11977, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_11595, c_11966])).
% 13.70/6.57  tff(c_32, plain, (![A_27]: (k5_relat_1(k6_relat_1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_89])).
% 13.70/6.57  tff(c_112, plain, (![A_27]: (k5_relat_1(k6_partfun1(k1_relat_1(A_27)), A_27)=A_27 | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_32])).
% 13.70/6.57  tff(c_1526, plain, (![A_160, B_161, C_162]: (k5_relat_1(k5_relat_1(A_160, B_161), C_162)=k5_relat_1(A_160, k5_relat_1(B_161, C_162)) | ~v1_relat_1(C_162) | ~v1_relat_1(B_161) | ~v1_relat_1(A_160))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.70/6.57  tff(c_1582, plain, (![A_27, C_162]: (k5_relat_1(k6_partfun1(k1_relat_1(A_27)), k5_relat_1(A_27, C_162))=k5_relat_1(A_27, C_162) | ~v1_relat_1(C_162) | ~v1_relat_1(A_27) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_27))) | ~v1_relat_1(A_27))), inference(superposition, [status(thm), theory('equality')], [c_112, c_1526])).
% 13.70/6.57  tff(c_12457, plain, (![A_464, C_465]: (k5_relat_1(k6_partfun1(k1_relat_1(A_464)), k5_relat_1(A_464, C_465))=k5_relat_1(A_464, C_465) | ~v1_relat_1(C_465) | ~v1_relat_1(A_464))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1582])).
% 13.70/6.57  tff(c_12493, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k5_relat_1('#skF_3', '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11977, c_12457])).
% 13.70/6.57  tff(c_12563, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1('#skF_1'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_223, c_11977, c_12493])).
% 13.70/6.57  tff(c_22, plain, (![A_14, B_16]: (k10_relat_1(A_14, k1_relat_1(B_16))=k1_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.70/6.57  tff(c_30, plain, (![A_26]: (k2_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_85])).
% 13.70/6.57  tff(c_113, plain, (![A_26]: (k2_relat_1(k6_partfun1(A_26))=A_26)), inference(demodulation, [status(thm), theory('equality')], [c_76, c_30])).
% 13.70/6.57  tff(c_34, plain, (![B_29, A_28]: (k5_relat_1(B_29, k6_relat_1(A_28))=B_29 | ~r1_tarski(k2_relat_1(B_29), A_28) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_95])).
% 13.70/6.57  tff(c_555, plain, (![B_121, A_122]: (k5_relat_1(B_121, k6_partfun1(A_122))=B_121 | ~r1_tarski(k2_relat_1(B_121), A_122) | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_34])).
% 13.70/6.57  tff(c_561, plain, (![A_26, A_122]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_122))=k6_partfun1(A_26) | ~r1_tarski(A_26, A_122) | ~v1_relat_1(k6_partfun1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_555])).
% 13.70/6.57  tff(c_567, plain, (![A_26, A_122]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_122))=k6_partfun1(A_26) | ~r1_tarski(A_26, A_122))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_561])).
% 13.70/6.57  tff(c_655, plain, (![A_127, B_128]: (k10_relat_1(A_127, k1_relat_1(B_128))=k1_relat_1(k5_relat_1(A_127, B_128)) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(cnfTransformation, [status(thm)], [f_65])).
% 13.70/6.57  tff(c_675, plain, (![A_127, A_26]: (k1_relat_1(k5_relat_1(A_127, k6_partfun1(A_26)))=k10_relat_1(A_127, A_26) | ~v1_relat_1(k6_partfun1(A_26)) | ~v1_relat_1(A_127))), inference(superposition, [status(thm), theory('equality')], [c_114, c_655])).
% 13.70/6.57  tff(c_733, plain, (![A_131, A_132]: (k1_relat_1(k5_relat_1(A_131, k6_partfun1(A_132)))=k10_relat_1(A_131, A_132) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_675])).
% 13.70/6.57  tff(c_769, plain, (![A_26, A_122]: (k10_relat_1(k6_partfun1(A_26), A_122)=k1_relat_1(k6_partfun1(A_26)) | ~v1_relat_1(k6_partfun1(A_26)) | ~r1_tarski(A_26, A_122))), inference(superposition, [status(thm), theory('equality')], [c_567, c_733])).
% 13.70/6.57  tff(c_788, plain, (![A_133, A_134]: (k10_relat_1(k6_partfun1(A_133), A_134)=A_133 | ~r1_tarski(A_133, A_134))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_114, c_769])).
% 13.70/6.57  tff(c_810, plain, (![A_133, B_16]: (k1_relat_1(k5_relat_1(k6_partfun1(A_133), B_16))=A_133 | ~r1_tarski(A_133, k1_relat_1(B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(k6_partfun1(A_133)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_788])).
% 13.70/6.57  tff(c_828, plain, (![A_133, B_16]: (k1_relat_1(k5_relat_1(k6_partfun1(A_133), B_16))=A_133 | ~r1_tarski(A_133, k1_relat_1(B_16)) | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_810])).
% 13.70/6.57  tff(c_12773, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(k6_partfun1('#skF_1'))) | ~v1_relat_1(k6_partfun1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_12563, c_828])).
% 13.70/6.57  tff(c_12795, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_114, c_114, c_12773])).
% 13.70/6.57  tff(c_12812, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_12795])).
% 13.70/6.57  tff(c_12825, plain, (~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_12812])).
% 13.70/6.57  tff(c_12829, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_286, c_12825])).
% 13.70/6.57  tff(c_12830, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_12795])).
% 13.70/6.57  tff(c_78, plain, (![A_63]: (m1_subset_1(A_63, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_63), k2_relat_1(A_63)))) | ~v1_funct_1(A_63) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_202])).
% 13.70/6.57  tff(c_935, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2'))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_927, c_78])).
% 13.70/6.57  tff(c_953, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_935])).
% 13.70/6.57  tff(c_58, plain, (![C_41, A_39, B_40]: (v4_relat_1(C_41, A_39) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_152])).
% 13.70/6.57  tff(c_1010, plain, (v4_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_953, c_58])).
% 13.70/6.57  tff(c_24, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.70/6.57  tff(c_1018, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1010, c_24])).
% 13.70/6.57  tff(c_1021, plain, (k7_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_1018])).
% 13.70/6.57  tff(c_18, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.70/6.57  tff(c_1037, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1021, c_18])).
% 13.70/6.57  tff(c_1047, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_927, c_1037])).
% 13.70/6.57  tff(c_10981, plain, (![A_383, B_384]: (k9_relat_1(k2_funct_1(A_383), k9_relat_1(A_383, B_384))=B_384 | ~r1_tarski(B_384, k1_relat_1(A_383)) | ~v2_funct_1(A_383) | ~v1_funct_1(A_383) | ~v1_relat_1(A_383))), inference(cnfTransformation, [status(thm)], [f_126])).
% 13.70/6.57  tff(c_11008, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1047, c_10981])).
% 13.70/6.57  tff(c_11033, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_6, c_11008])).
% 13.70/6.57  tff(c_293, plain, (![B_99, A_100]: (k7_relat_1(B_99, A_100)=B_99 | ~v4_relat_1(B_99, A_100) | ~v1_relat_1(B_99))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.70/6.57  tff(c_299, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_286, c_293])).
% 13.70/6.57  tff(c_308, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_299])).
% 13.70/6.57  tff(c_316, plain, (![B_101, A_102]: (k2_relat_1(k7_relat_1(B_101, A_102))=k9_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_54])).
% 13.70/6.57  tff(c_328, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_308, c_316])).
% 13.70/6.57  tff(c_332, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_328])).
% 13.70/6.57  tff(c_928, plain, (k9_relat_1('#skF_3', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_927, c_332])).
% 13.70/6.57  tff(c_11011, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_928, c_10981])).
% 13.70/6.57  tff(c_11035, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_11011])).
% 13.70/6.57  tff(c_11220, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11033, c_11035])).
% 13.70/6.57  tff(c_11221, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_11220])).
% 13.70/6.57  tff(c_12839, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_12830, c_11221])).
% 13.70/6.57  tff(c_12856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_12839])).
% 13.70/6.57  tff(c_12857, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_11220])).
% 13.70/6.57  tff(c_12894, plain, (![A_14]: (k1_relat_1(k5_relat_1(A_14, '#skF_3'))=k10_relat_1(A_14, '#skF_1') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_12857, c_22])).
% 13.70/6.57  tff(c_13976, plain, (![A_528]: (k1_relat_1(k5_relat_1(A_528, '#skF_3'))=k10_relat_1(A_528, '#skF_1') | ~v1_relat_1(A_528))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_12894])).
% 13.70/6.57  tff(c_14048, plain, (k1_relat_1(k6_partfun1(k2_relat_1('#skF_3')))=k10_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_108, c_13976])).
% 13.70/6.57  tff(c_14072, plain, (k10_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_2' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_114, c_927, c_14048])).
% 13.70/6.57  tff(c_14077, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_14072])).
% 13.70/6.57  tff(c_14101, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_38, c_14077])).
% 13.70/6.57  tff(c_14105, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_14101])).
% 13.70/6.57  tff(c_14107, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_14072])).
% 13.70/6.57  tff(c_12859, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12857, c_11033])).
% 13.70/6.57  tff(c_50, plain, (![A_37]: (k1_relat_1(k2_funct_1(A_37))=k2_relat_1(A_37) | ~v2_funct_1(A_37) | ~v1_funct_1(A_37) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_136])).
% 13.70/6.57  tff(c_185, plain, (![A_81]: (k5_relat_1(k6_partfun1(k1_relat_1(A_81)), A_81)=A_81 | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_32])).
% 13.70/6.57  tff(c_194, plain, (![A_26]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_26))=k6_partfun1(A_26) | ~v1_relat_1(k6_partfun1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_185])).
% 13.70/6.57  tff(c_198, plain, (![A_26]: (k5_relat_1(k6_partfun1(A_26), k6_partfun1(A_26))=k6_partfun1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_194])).
% 13.70/6.57  tff(c_54, plain, (![A_38]: (k5_relat_1(A_38, k2_funct_1(A_38))=k6_relat_1(k1_relat_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_146])).
% 13.70/6.57  tff(c_107, plain, (![A_38]: (k5_relat_1(A_38, k2_funct_1(A_38))=k6_partfun1(k1_relat_1(A_38)) | ~v2_funct_1(A_38) | ~v1_funct_1(A_38) | ~v1_relat_1(A_38))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_54])).
% 13.70/6.57  tff(c_12915, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12857, c_112])).
% 13.70/6.57  tff(c_12943, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_12915])).
% 13.70/6.57  tff(c_26, plain, (![A_19, B_23, C_25]: (k5_relat_1(k5_relat_1(A_19, B_23), C_25)=k5_relat_1(A_19, k5_relat_1(B_23, C_25)) | ~v1_relat_1(C_25) | ~v1_relat_1(B_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.70/6.57  tff(c_12999, plain, (![C_25]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_25))=k5_relat_1('#skF_3', C_25) | ~v1_relat_1(C_25) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_12943, c_26])).
% 13.70/6.57  tff(c_14182, plain, (![C_541]: (k5_relat_1(k6_partfun1('#skF_1'), k5_relat_1('#skF_3', C_541))=k5_relat_1('#skF_3', C_541) | ~v1_relat_1(C_541))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_226, c_12999])).
% 13.70/6.57  tff(c_14213, plain, (k5_relat_1(k6_partfun1('#skF_1'), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_107, c_14182])).
% 13.70/6.57  tff(c_14230, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_14107, c_198, c_12857, c_14213])).
% 13.70/6.57  tff(c_1348, plain, (![B_152, A_153]: (k9_relat_1(B_152, k10_relat_1(B_152, A_153))=A_153 | ~r1_tarski(A_153, k2_relat_1(B_152)) | ~v1_funct_1(B_152) | ~v1_relat_1(B_152))), inference(cnfTransformation, [status(thm)], [f_115])).
% 13.70/6.57  tff(c_1350, plain, (![A_153]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_153))=A_153 | ~r1_tarski(A_153, '#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_927, c_1348])).
% 13.70/6.57  tff(c_1369, plain, (![A_154]: (k9_relat_1('#skF_3', k10_relat_1('#skF_3', A_154))=A_154 | ~r1_tarski(A_154, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_1350])).
% 13.70/6.57  tff(c_1382, plain, (![B_16]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_16)))=k1_relat_1(B_16) | ~r1_tarski(k1_relat_1(B_16), '#skF_2') | ~v1_relat_1(B_16) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1369])).
% 13.70/6.57  tff(c_1392, plain, (![B_16]: (k9_relat_1('#skF_3', k1_relat_1(k5_relat_1('#skF_3', B_16)))=k1_relat_1(B_16) | ~r1_tarski(k1_relat_1(B_16), '#skF_2') | ~v1_relat_1(B_16))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_1382])).
% 13.70/6.57  tff(c_14242, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1(k2_funct_1('#skF_3')) | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14230, c_1392])).
% 13.70/6.57  tff(c_14257, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2' | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_928, c_114, c_14242])).
% 13.70/6.57  tff(c_14265, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_14257])).
% 13.70/6.57  tff(c_14268, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_50, c_14265])).
% 13.70/6.57  tff(c_14274, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_6, c_927, c_14268])).
% 13.70/6.57  tff(c_14275, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_14257])).
% 13.70/6.57  tff(c_16, plain, (![A_10]: (k9_relat_1(A_10, k1_relat_1(A_10))=k2_relat_1(A_10) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 13.70/6.57  tff(c_14341, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14275, c_16])).
% 13.70/6.57  tff(c_14375, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_12859, c_14341])).
% 13.70/6.57  tff(c_568, plain, (![B_121]: (k5_relat_1(B_121, k6_partfun1(k2_relat_1(B_121)))=B_121 | ~v1_relat_1(B_121))), inference(resolution, [status(thm)], [c_6, c_555])).
% 13.70/6.57  tff(c_14407, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_14375, c_568])).
% 13.70/6.57  tff(c_14438, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14107, c_14407])).
% 13.70/6.57  tff(c_285, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_96, c_274])).
% 13.70/6.57  tff(c_66, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (m1_subset_1(k1_partfun1(A_49, B_50, C_51, D_52, E_53, F_54), k1_zfmisc_1(k2_zfmisc_1(A_49, D_52))) | ~m1_subset_1(F_54, k1_zfmisc_1(k2_zfmisc_1(C_51, D_52))) | ~v1_funct_1(F_54) | ~m1_subset_1(E_53, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(E_53))), inference(cnfTransformation, [status(thm)], [f_176])).
% 13.70/6.57  tff(c_12946, plain, (![D_470, C_471, A_472, B_473]: (D_470=C_471 | ~r2_relset_1(A_472, B_473, C_471, D_470) | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))))), inference(cnfTransformation, [status(thm)], [f_164])).
% 13.70/6.57  tff(c_12956, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_92, c_12946])).
% 13.70/6.57  tff(c_12973, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_12956])).
% 13.70/6.57  tff(c_13015, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_12973])).
% 13.70/6.57  tff(c_13617, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_66, c_13015])).
% 13.70/6.57  tff(c_13621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_102, c_100, c_96, c_13617])).
% 13.70/6.57  tff(c_13622, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_12973])).
% 13.70/6.57  tff(c_13958, plain, (![C_524, E_525, B_522, A_527, D_526, F_523]: (k1_partfun1(A_527, B_522, C_524, D_526, E_525, F_523)=k5_relat_1(E_525, F_523) | ~m1_subset_1(F_523, k1_zfmisc_1(k2_zfmisc_1(C_524, D_526))) | ~v1_funct_1(F_523) | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(A_527, B_522))) | ~v1_funct_1(E_525))), inference(cnfTransformation, [status(thm)], [f_190])).
% 13.70/6.57  tff(c_13964, plain, (![A_527, B_522, E_525]: (k1_partfun1(A_527, B_522, '#skF_2', '#skF_1', E_525, '#skF_4')=k5_relat_1(E_525, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_525, k1_zfmisc_1(k2_zfmisc_1(A_527, B_522))) | ~v1_funct_1(E_525))), inference(resolution, [status(thm)], [c_96, c_13958])).
% 13.70/6.57  tff(c_14961, plain, (![A_551, B_552, E_553]: (k1_partfun1(A_551, B_552, '#skF_2', '#skF_1', E_553, '#skF_4')=k5_relat_1(E_553, '#skF_4') | ~m1_subset_1(E_553, k1_zfmisc_1(k2_zfmisc_1(A_551, B_552))) | ~v1_funct_1(E_553))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_13964])).
% 13.70/6.57  tff(c_14982, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_102, c_14961])).
% 13.70/6.57  tff(c_14997, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_106, c_13622, c_14982])).
% 13.70/6.57  tff(c_15007, plain, (k9_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14997, c_1392])).
% 13.70/6.57  tff(c_15018, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_928, c_114, c_15007])).
% 13.70/6.57  tff(c_15022, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_15018])).
% 13.70/6.57  tff(c_15025, plain, (~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_12, c_15022])).
% 13.70/6.57  tff(c_15029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_285, c_15025])).
% 13.70/6.57  tff(c_15030, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_15018])).
% 13.70/6.57  tff(c_15077, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15030, c_112])).
% 13.70/6.57  tff(c_15109, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_15077])).
% 13.70/6.57  tff(c_21799, plain, (![A_666, C_667]: (k5_relat_1(k6_partfun1(k2_relat_1(A_666)), C_667)=k5_relat_1(k2_funct_1(A_666), k5_relat_1(A_666, C_667)) | ~v1_relat_1(C_667) | ~v1_relat_1(A_666) | ~v1_relat_1(k2_funct_1(A_666)) | ~v2_funct_1(A_666) | ~v1_funct_1(A_666) | ~v1_relat_1(A_666))), inference(superposition, [status(thm), theory('equality')], [c_108, c_1526])).
% 13.70/6.57  tff(c_21991, plain, (![C_667]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_667))=k5_relat_1(k6_partfun1('#skF_2'), C_667) | ~v1_relat_1(C_667) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_927, c_21799])).
% 13.70/6.57  tff(c_28144, plain, (![C_798]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_798))=k5_relat_1(k6_partfun1('#skF_2'), C_798) | ~v1_relat_1(C_798))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_106, c_90, c_14107, c_226, c_21991])).
% 13.70/6.57  tff(c_28202, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_14997, c_28144])).
% 13.70/6.57  tff(c_28256, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_14438, c_15109, c_28202])).
% 13.70/6.57  tff(c_28258, plain, $false, inference(negUnitSimplification, [status(thm)], [c_84, c_28256])).
% 13.70/6.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.70/6.57  
% 13.70/6.57  Inference rules
% 13.70/6.57  ----------------------
% 13.70/6.57  #Ref     : 0
% 13.70/6.57  #Sup     : 6175
% 13.70/6.57  #Fact    : 0
% 13.70/6.57  #Define  : 0
% 13.70/6.57  #Split   : 39
% 13.70/6.57  #Chain   : 0
% 13.70/6.57  #Close   : 0
% 13.70/6.57  
% 13.70/6.57  Ordering : KBO
% 13.70/6.57  
% 13.70/6.57  Simplification rules
% 13.70/6.57  ----------------------
% 13.70/6.57  #Subsume      : 349
% 13.70/6.57  #Demod        : 10990
% 13.70/6.57  #Tautology    : 2236
% 13.70/6.57  #SimpNegUnit  : 2
% 13.70/6.57  #BackRed      : 168
% 13.70/6.57  
% 13.70/6.57  #Partial instantiations: 0
% 13.70/6.57  #Strategies tried      : 1
% 13.70/6.57  
% 13.70/6.57  Timing (in seconds)
% 13.70/6.57  ----------------------
% 13.70/6.58  Preprocessing        : 0.37
% 13.70/6.58  Parsing              : 0.20
% 13.70/6.58  CNF conversion       : 0.03
% 13.70/6.58  Main loop            : 5.34
% 13.70/6.58  Inferencing          : 1.30
% 13.70/6.58  Reduction            : 2.64
% 13.70/6.58  Demodulation         : 2.21
% 13.70/6.58  BG Simplification    : 0.13
% 13.70/6.58  Subsumption          : 0.98
% 13.70/6.58  Abstraction          : 0.17
% 13.70/6.58  MUC search           : 0.00
% 13.70/6.58  Cooper               : 0.00
% 13.70/6.58  Total                : 5.78
% 13.70/6.58  Index Insertion      : 0.00
% 13.70/6.58  Index Deletion       : 0.00
% 13.70/6.58  Index Matching       : 0.00
% 13.70/6.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
