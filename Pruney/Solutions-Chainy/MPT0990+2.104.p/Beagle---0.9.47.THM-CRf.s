%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:11 EST 2020

% Result     : Theorem 10.65s
% Output     : CNFRefutation 10.65s
% Verified   : 
% Statistics : Number of formulae       :  166 (2037 expanded)
%              Number of leaves         :   50 ( 741 expanded)
%              Depth                    :   27
%              Number of atoms          :  326 (6347 expanded)
%              Number of equality atoms :   76 (1615 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_198,negated_conjecture,(
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

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_132,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_98,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => v1_relat_1(k4_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

tff(f_172,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_78,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_80,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_156,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_160,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_144,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_170,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_136,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_126,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_16,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_151,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_157,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_82,c_151])).

tff(c_166,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_157])).

tff(c_204,plain,(
    ! [C_80,A_81,B_82] :
      ( v4_relat_1(C_80,A_81)
      | ~ m1_subset_1(C_80,k1_zfmisc_1(k2_zfmisc_1(A_81,B_82))) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_215,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_204])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_160,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_88,c_151])).

tff(c_169,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_160])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_266,plain,(
    ! [A_93] :
      ( k4_relat_1(A_93) = k2_funct_1(A_93)
      | ~ v2_funct_1(A_93)
      | ~ v1_funct_1(A_93)
      | ~ v1_relat_1(A_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_269,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_266])).

tff(c_272,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_92,c_269])).

tff(c_216,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_204])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_relat_1(k4_relat_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_68,plain,(
    ! [A_56] : k6_relat_1(A_56) = k6_partfun1(A_56) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_26,plain,(
    ! [A_24] : k2_relat_1(k6_relat_1(A_24)) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_98,plain,(
    ! [A_24] : k2_relat_1(k6_partfun1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_26])).

tff(c_28,plain,(
    ! [A_25] : k4_relat_1(k6_relat_1(A_25)) = k6_relat_1(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    ! [A_25] : k4_relat_1(k6_partfun1(A_25)) = k6_partfun1(A_25) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_68,c_28])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_6154,plain,(
    ! [E_334,C_329,B_333,D_330,A_332,F_331] :
      ( m1_subset_1(k1_partfun1(A_332,B_333,C_329,D_330,E_334,F_331),k1_zfmisc_1(k2_zfmisc_1(A_332,D_330)))
      | ~ m1_subset_1(F_331,k1_zfmisc_1(k2_zfmisc_1(C_329,D_330)))
      | ~ v1_funct_1(F_331)
      | ~ m1_subset_1(E_334,k1_zfmisc_1(k2_zfmisc_1(A_332,B_333)))
      | ~ v1_funct_1(E_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_64,plain,(
    ! [A_49] : m1_subset_1(k6_partfun1(A_49),k1_zfmisc_1(k2_zfmisc_1(A_49,A_49))) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_5336,plain,(
    ! [D_283,C_284,A_285,B_286] :
      ( D_283 = C_284
      | ~ r2_relset_1(A_285,B_286,C_284,D_283)
      | ~ m1_subset_1(D_283,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ m1_subset_1(C_284,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_5344,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_5336])).

tff(c_5359,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5344])).

tff(c_5477,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_5359])).

tff(c_6157,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6154,c_5477])).

tff(c_6185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_6157])).

tff(c_6186,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5359])).

tff(c_6749,plain,(
    ! [D_365,A_361,B_363,E_360,C_362,F_364] :
      ( k1_partfun1(A_361,B_363,C_362,D_365,E_360,F_364) = k5_relat_1(E_360,F_364)
      | ~ m1_subset_1(F_364,k1_zfmisc_1(k2_zfmisc_1(C_362,D_365)))
      | ~ v1_funct_1(F_364)
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_1(E_360) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_6753,plain,(
    ! [A_361,B_363,E_360] :
      ( k1_partfun1(A_361,B_363,'#skF_2','#skF_1',E_360,'#skF_4') = k5_relat_1(E_360,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_360,k1_zfmisc_1(k2_zfmisc_1(A_361,B_363)))
      | ~ v1_funct_1(E_360) ) ),
    inference(resolution,[status(thm)],[c_82,c_6749])).

tff(c_7078,plain,(
    ! [A_388,B_389,E_390] :
      ( k1_partfun1(A_388,B_389,'#skF_2','#skF_1',E_390,'#skF_4') = k5_relat_1(E_390,'#skF_4')
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_388,B_389)))
      | ~ v1_funct_1(E_390) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_6753])).

tff(c_7090,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_7078])).

tff(c_7098,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_6186,c_7090])).

tff(c_612,plain,(
    ! [B_117,A_118] :
      ( k5_relat_1(k4_relat_1(B_117),k4_relat_1(A_118)) = k4_relat_1(k5_relat_1(A_118,B_117))
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1(A_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_627,plain,(
    ! [B_117] :
      ( k5_relat_1(k4_relat_1(B_117),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_117))
      | ~ v1_relat_1(B_117)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_612])).

tff(c_639,plain,(
    ! [B_117] :
      ( k5_relat_1(k4_relat_1(B_117),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_627])).

tff(c_276,plain,
    ( v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_14])).

tff(c_280,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_276])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_30,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_relat_1(A_26),B_27) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_282,plain,(
    ! [A_94,B_95] :
      ( k5_relat_1(k6_partfun1(A_94),B_95) = B_95
      | ~ r1_tarski(k1_relat_1(B_95),A_94)
      | ~ v1_relat_1(B_95) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30])).

tff(c_296,plain,(
    ! [B_95] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(B_95)),B_95) = B_95
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_6,c_282])).

tff(c_154,plain,(
    ! [A_49] :
      ( v1_relat_1(k6_partfun1(A_49))
      | ~ v1_relat_1(k2_zfmisc_1(A_49,A_49)) ) ),
    inference(resolution,[status(thm)],[c_64,c_151])).

tff(c_163,plain,(
    ! [A_49] : v1_relat_1(k6_partfun1(A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_154])).

tff(c_624,plain,(
    ! [A_118] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_118)) = k4_relat_1(k5_relat_1(A_118,'#skF_3'))
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_118) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_612])).

tff(c_644,plain,(
    ! [A_119] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k4_relat_1(A_119)) = k4_relat_1(k5_relat_1(A_119,'#skF_3'))
      | ~ v1_relat_1(A_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_624])).

tff(c_659,plain,(
    ! [A_25] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_25)) = k4_relat_1(k5_relat_1(k6_partfun1(A_25),'#skF_3'))
      | ~ v1_relat_1(k6_partfun1(A_25)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_644])).

tff(c_712,plain,(
    ! [A_121] : k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_121)) = k4_relat_1(k5_relat_1(k6_partfun1(A_121),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_659])).

tff(c_473,plain,(
    ! [A_108,B_109] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_108,B_109)),k2_relat_1(B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_496,plain,(
    ! [A_108,A_24] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_108,k6_partfun1(A_24))),A_24)
      | ~ v1_relat_1(k6_partfun1(A_24))
      | ~ v1_relat_1(A_108) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_473])).

tff(c_509,plain,(
    ! [A_108,A_24] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_108,k6_partfun1(A_24))),A_24)
      | ~ v1_relat_1(A_108) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_496])).

tff(c_718,plain,(
    ! [A_121] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k6_partfun1(A_121),'#skF_3'))),A_121)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_712,c_509])).

tff(c_743,plain,(
    ! [A_122] : r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k6_partfun1(A_122),'#skF_3'))),A_122) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_718])).

tff(c_753,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1('#skF_3')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_743])).

tff(c_758,plain,(
    r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_272,c_753])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_198])).

tff(c_540,plain,(
    ! [A_112,B_113,C_114] :
      ( k2_relset_1(A_112,B_113,C_114) = k2_relat_1(C_114)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_112,B_113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_549,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_540])).

tff(c_554,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_549])).

tff(c_44,plain,(
    ! [A_32] :
      ( k5_relat_1(k2_funct_1(A_32),A_32) = k6_relat_1(k2_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_94,plain,(
    ! [A_32] :
      ( k5_relat_1(k2_funct_1(A_32),A_32) = k6_partfun1(k2_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_44])).

tff(c_18,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_11,B_13)),k2_relat_1(B_13))
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_650,plain,(
    ! [A_119] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_119,'#skF_3'))),k2_relat_1(k4_relat_1(A_119)))
      | ~ v1_relat_1(k4_relat_1(A_119))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(A_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_644,c_18])).

tff(c_1158,plain,(
    ! [A_131] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_131,'#skF_3'))),k2_relat_1(k4_relat_1(A_131)))
      | ~ v1_relat_1(k4_relat_1(A_131))
      | ~ v1_relat_1(A_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_650])).

tff(c_1179,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(k2_relat_1('#skF_3')))),k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1158])).

tff(c_1206,plain,
    ( r1_tarski('#skF_2',k2_relat_1(k4_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_92,c_76,c_280,c_554,c_98,c_97,c_1179])).

tff(c_1285,plain,(
    ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_1419,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_14,c_1285])).

tff(c_1423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_1419])).

tff(c_1425,plain,(
    v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_46,plain,(
    ! [A_32] :
      ( k5_relat_1(A_32,k2_funct_1(A_32)) = k6_relat_1(k1_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_93,plain,(
    ! [A_32] :
      ( k5_relat_1(A_32,k2_funct_1(A_32)) = k6_partfun1(k1_relat_1(A_32))
      | ~ v2_funct_1(A_32)
      | ~ v1_funct_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_46])).

tff(c_685,plain,(
    ! [B_120] :
      ( k5_relat_1(k4_relat_1(B_120),k2_funct_1('#skF_3')) = k4_relat_1(k5_relat_1('#skF_3',B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_627])).

tff(c_691,plain,(
    ! [B_120] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3',B_120))),k2_relat_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(k4_relat_1(B_120))
      | ~ v1_relat_1(B_120) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_685,c_18])).

tff(c_1429,plain,(
    ! [B_137] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3',B_137))),k2_relat_1(k2_funct_1('#skF_3')))
      | ~ v1_relat_1(k4_relat_1(B_137))
      | ~ v1_relat_1(B_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_691])).

tff(c_1438,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(k1_relat_1('#skF_3')))),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_1429])).

tff(c_1453,plain,(
    r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_92,c_76,c_280,c_1425,c_98,c_97,c_1438])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1467,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_3')),k1_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1453,c_2])).

tff(c_1479,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_1467])).

tff(c_1504,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_11,k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1479,c_18])).

tff(c_1737,plain,(
    ! [A_141] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_141,k2_funct_1('#skF_3'))),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(A_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_1504])).

tff(c_1757,plain,(
    ! [B_117] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3',B_117))),k1_relat_1('#skF_3'))
      | ~ v1_relat_1(k4_relat_1(B_117))
      | ~ v1_relat_1(B_117) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_639,c_1737])).

tff(c_7102,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1('#skF_1'))),k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7098,c_1757])).

tff(c_7112,plain,
    ( r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_98,c_97,c_7102])).

tff(c_7125,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7112])).

tff(c_7289,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_7125])).

tff(c_7293,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_7289])).

tff(c_7294,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_7112])).

tff(c_217,plain,(
    ! [B_83,A_84] :
      ( r1_tarski(k1_relat_1(B_83),A_84)
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_223,plain,(
    ! [B_83,A_84] :
      ( k1_relat_1(B_83) = A_84
      | ~ r1_tarski(A_84,k1_relat_1(B_83))
      | ~ v4_relat_1(B_83,A_84)
      | ~ v1_relat_1(B_83) ) ),
    inference(resolution,[status(thm)],[c_217,c_2])).

tff(c_7298,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7294,c_223])).

tff(c_7308,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_216,c_7298])).

tff(c_96,plain,(
    ! [A_26,B_27] :
      ( k5_relat_1(k6_partfun1(A_26),B_27) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_30])).

tff(c_1462,plain,
    ( k5_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1453,c_96])).

tff(c_1473,plain,(
    k5_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_1462])).

tff(c_1527,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1479,c_1473])).

tff(c_7328,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7308,c_1527])).

tff(c_667,plain,(
    ! [A_25] : k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1(A_25)) = k4_relat_1(k5_relat_1(k6_partfun1(A_25),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_659])).

tff(c_1601,plain,(
    ! [A_138,B_139,C_140] :
      ( k5_relat_1(k5_relat_1(A_138,B_139),C_140) = k5_relat_1(A_138,k5_relat_1(B_139,C_140))
      | ~ v1_relat_1(C_140)
      | ~ v1_relat_1(B_139)
      | ~ v1_relat_1(A_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_11922,plain,(
    ! [A_481,C_482] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_481)),C_482) = k5_relat_1(k2_funct_1(A_481),k5_relat_1(A_481,C_482))
      | ~ v1_relat_1(C_482)
      | ~ v1_relat_1(A_481)
      | ~ v1_relat_1(k2_funct_1(A_481))
      | ~ v2_funct_1(A_481)
      | ~ v1_funct_1(A_481)
      | ~ v1_relat_1(A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_1601])).

tff(c_12271,plain,(
    ! [C_482] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_482)) = k5_relat_1(k6_partfun1('#skF_2'),C_482)
      | ~ v1_relat_1(C_482)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_554,c_11922])).

tff(c_15210,plain,(
    ! [C_539] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_539)) = k5_relat_1(k6_partfun1('#skF_2'),C_539)
      | ~ v1_relat_1(C_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_92,c_76,c_280,c_169,c_12271])).

tff(c_15286,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7098,c_15210])).

tff(c_15343,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_272,c_7328,c_667,c_15286])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_293,plain,(
    ! [A_6,B_7] :
      ( k5_relat_1(k6_partfun1(A_6),B_7) = B_7
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_282])).

tff(c_15991,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15343,c_293])).

tff(c_16018,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_215,c_15991])).

tff(c_16020,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_16018])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:59:09 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.65/4.08  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.65/4.09  
% 10.65/4.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.65/4.09  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.65/4.09  
% 10.65/4.09  %Foreground sorts:
% 10.65/4.09  
% 10.65/4.09  
% 10.65/4.09  %Background operators:
% 10.65/4.09  
% 10.65/4.09  
% 10.65/4.09  %Foreground operators:
% 10.65/4.09  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.65/4.09  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.65/4.09  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.65/4.09  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.65/4.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.65/4.09  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.65/4.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.65/4.09  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.65/4.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.65/4.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.65/4.09  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.65/4.09  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.65/4.09  tff('#skF_2', type, '#skF_2': $i).
% 10.65/4.09  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.65/4.09  tff('#skF_3', type, '#skF_3': $i).
% 10.65/4.09  tff('#skF_1', type, '#skF_1': $i).
% 10.65/4.09  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.65/4.09  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.65/4.09  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.65/4.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.65/4.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.65/4.09  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.65/4.09  tff('#skF_4', type, '#skF_4': $i).
% 10.65/4.09  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.65/4.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.65/4.09  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.65/4.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.65/4.09  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 10.65/4.09  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.65/4.09  
% 10.65/4.11  tff(f_198, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.65/4.11  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.65/4.11  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.65/4.11  tff(f_132, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.65/4.11  tff(f_98, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 10.65/4.11  tff(f_48, axiom, (![A]: (v1_relat_1(A) => v1_relat_1(k4_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relat_1)).
% 10.65/4.11  tff(f_172, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.65/4.11  tff(f_78, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.65/4.11  tff(f_80, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 10.65/4.11  tff(f_156, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.65/4.11  tff(f_160, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.65/4.11  tff(f_144, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.65/4.11  tff(f_170, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.65/4.11  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 10.65/4.11  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.65/4.11  tff(f_86, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 10.65/4.11  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_relat_1)).
% 10.65/4.11  tff(f_136, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.65/4.11  tff(f_126, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.65/4.11  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 10.65/4.11  tff(f_74, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 10.65/4.11  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 10.65/4.11  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_151, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.65/4.11  tff(c_157, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_82, c_151])).
% 10.65/4.11  tff(c_166, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_157])).
% 10.65/4.11  tff(c_204, plain, (![C_80, A_81, B_82]: (v4_relat_1(C_80, A_81) | ~m1_subset_1(C_80, k1_zfmisc_1(k2_zfmisc_1(A_81, B_82))))), inference(cnfTransformation, [status(thm)], [f_132])).
% 10.65/4.11  tff(c_215, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_204])).
% 10.65/4.11  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_160, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_88, c_151])).
% 10.65/4.11  tff(c_169, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_160])).
% 10.65/4.11  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_266, plain, (![A_93]: (k4_relat_1(A_93)=k2_funct_1(A_93) | ~v2_funct_1(A_93) | ~v1_funct_1(A_93) | ~v1_relat_1(A_93))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.65/4.11  tff(c_269, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_266])).
% 10.65/4.11  tff(c_272, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_169, c_92, c_269])).
% 10.65/4.11  tff(c_216, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_88, c_204])).
% 10.65/4.11  tff(c_14, plain, (![A_8]: (v1_relat_1(k4_relat_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.65/4.11  tff(c_68, plain, (![A_56]: (k6_relat_1(A_56)=k6_partfun1(A_56))), inference(cnfTransformation, [status(thm)], [f_172])).
% 10.65/4.11  tff(c_26, plain, (![A_24]: (k2_relat_1(k6_relat_1(A_24))=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 10.65/4.11  tff(c_98, plain, (![A_24]: (k2_relat_1(k6_partfun1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_26])).
% 10.65/4.11  tff(c_28, plain, (![A_25]: (k4_relat_1(k6_relat_1(A_25))=k6_relat_1(A_25))), inference(cnfTransformation, [status(thm)], [f_80])).
% 10.65/4.11  tff(c_97, plain, (![A_25]: (k4_relat_1(k6_partfun1(A_25))=k6_partfun1(A_25))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_68, c_28])).
% 10.65/4.11  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_6154, plain, (![E_334, C_329, B_333, D_330, A_332, F_331]: (m1_subset_1(k1_partfun1(A_332, B_333, C_329, D_330, E_334, F_331), k1_zfmisc_1(k2_zfmisc_1(A_332, D_330))) | ~m1_subset_1(F_331, k1_zfmisc_1(k2_zfmisc_1(C_329, D_330))) | ~v1_funct_1(F_331) | ~m1_subset_1(E_334, k1_zfmisc_1(k2_zfmisc_1(A_332, B_333))) | ~v1_funct_1(E_334))), inference(cnfTransformation, [status(thm)], [f_156])).
% 10.65/4.11  tff(c_64, plain, (![A_49]: (m1_subset_1(k6_partfun1(A_49), k1_zfmisc_1(k2_zfmisc_1(A_49, A_49))))), inference(cnfTransformation, [status(thm)], [f_160])).
% 10.65/4.11  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_5336, plain, (![D_283, C_284, A_285, B_286]: (D_283=C_284 | ~r2_relset_1(A_285, B_286, C_284, D_283) | ~m1_subset_1(D_283, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~m1_subset_1(C_284, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 10.65/4.11  tff(c_5344, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_5336])).
% 10.65/4.11  tff(c_5359, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5344])).
% 10.65/4.11  tff(c_5477, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_5359])).
% 10.65/4.11  tff(c_6157, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6154, c_5477])).
% 10.65/4.11  tff(c_6185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_6157])).
% 10.65/4.11  tff(c_6186, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5359])).
% 10.65/4.11  tff(c_6749, plain, (![D_365, A_361, B_363, E_360, C_362, F_364]: (k1_partfun1(A_361, B_363, C_362, D_365, E_360, F_364)=k5_relat_1(E_360, F_364) | ~m1_subset_1(F_364, k1_zfmisc_1(k2_zfmisc_1(C_362, D_365))) | ~v1_funct_1(F_364) | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_1(E_360))), inference(cnfTransformation, [status(thm)], [f_170])).
% 10.65/4.11  tff(c_6753, plain, (![A_361, B_363, E_360]: (k1_partfun1(A_361, B_363, '#skF_2', '#skF_1', E_360, '#skF_4')=k5_relat_1(E_360, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_360, k1_zfmisc_1(k2_zfmisc_1(A_361, B_363))) | ~v1_funct_1(E_360))), inference(resolution, [status(thm)], [c_82, c_6749])).
% 10.65/4.11  tff(c_7078, plain, (![A_388, B_389, E_390]: (k1_partfun1(A_388, B_389, '#skF_2', '#skF_1', E_390, '#skF_4')=k5_relat_1(E_390, '#skF_4') | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_388, B_389))) | ~v1_funct_1(E_390))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_6753])).
% 10.65/4.11  tff(c_7090, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_7078])).
% 10.65/4.11  tff(c_7098, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_6186, c_7090])).
% 10.65/4.11  tff(c_612, plain, (![B_117, A_118]: (k5_relat_1(k4_relat_1(B_117), k4_relat_1(A_118))=k4_relat_1(k5_relat_1(A_118, B_117)) | ~v1_relat_1(B_117) | ~v1_relat_1(A_118))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.65/4.11  tff(c_627, plain, (![B_117]: (k5_relat_1(k4_relat_1(B_117), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_117)) | ~v1_relat_1(B_117) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_272, c_612])).
% 10.65/4.11  tff(c_639, plain, (![B_117]: (k5_relat_1(k4_relat_1(B_117), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_117)) | ~v1_relat_1(B_117))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_627])).
% 10.65/4.11  tff(c_276, plain, (v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_272, c_14])).
% 10.65/4.11  tff(c_280, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_276])).
% 10.65/4.11  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.65/4.11  tff(c_30, plain, (![A_26, B_27]: (k5_relat_1(k6_relat_1(A_26), B_27)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.65/4.11  tff(c_282, plain, (![A_94, B_95]: (k5_relat_1(k6_partfun1(A_94), B_95)=B_95 | ~r1_tarski(k1_relat_1(B_95), A_94) | ~v1_relat_1(B_95))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30])).
% 10.65/4.11  tff(c_296, plain, (![B_95]: (k5_relat_1(k6_partfun1(k1_relat_1(B_95)), B_95)=B_95 | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_6, c_282])).
% 10.65/4.11  tff(c_154, plain, (![A_49]: (v1_relat_1(k6_partfun1(A_49)) | ~v1_relat_1(k2_zfmisc_1(A_49, A_49)))), inference(resolution, [status(thm)], [c_64, c_151])).
% 10.65/4.11  tff(c_163, plain, (![A_49]: (v1_relat_1(k6_partfun1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_154])).
% 10.65/4.11  tff(c_624, plain, (![A_118]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_118))=k4_relat_1(k5_relat_1(A_118, '#skF_3')) | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_118))), inference(superposition, [status(thm), theory('equality')], [c_272, c_612])).
% 10.65/4.11  tff(c_644, plain, (![A_119]: (k5_relat_1(k2_funct_1('#skF_3'), k4_relat_1(A_119))=k4_relat_1(k5_relat_1(A_119, '#skF_3')) | ~v1_relat_1(A_119))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_624])).
% 10.65/4.11  tff(c_659, plain, (![A_25]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_25))=k4_relat_1(k5_relat_1(k6_partfun1(A_25), '#skF_3')) | ~v1_relat_1(k6_partfun1(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_644])).
% 10.65/4.11  tff(c_712, plain, (![A_121]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_121))=k4_relat_1(k5_relat_1(k6_partfun1(A_121), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_659])).
% 10.65/4.11  tff(c_473, plain, (![A_108, B_109]: (r1_tarski(k2_relat_1(k5_relat_1(A_108, B_109)), k2_relat_1(B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_108))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.65/4.11  tff(c_496, plain, (![A_108, A_24]: (r1_tarski(k2_relat_1(k5_relat_1(A_108, k6_partfun1(A_24))), A_24) | ~v1_relat_1(k6_partfun1(A_24)) | ~v1_relat_1(A_108))), inference(superposition, [status(thm), theory('equality')], [c_98, c_473])).
% 10.65/4.11  tff(c_509, plain, (![A_108, A_24]: (r1_tarski(k2_relat_1(k5_relat_1(A_108, k6_partfun1(A_24))), A_24) | ~v1_relat_1(A_108))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_496])).
% 10.65/4.11  tff(c_718, plain, (![A_121]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k6_partfun1(A_121), '#skF_3'))), A_121) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_712, c_509])).
% 10.65/4.11  tff(c_743, plain, (![A_122]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(k6_partfun1(A_122), '#skF_3'))), A_122))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_718])).
% 10.65/4.11  tff(c_753, plain, (r1_tarski(k2_relat_1(k4_relat_1('#skF_3')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_296, c_743])).
% 10.65/4.11  tff(c_758, plain, (r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_272, c_753])).
% 10.65/4.11  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_198])).
% 10.65/4.11  tff(c_540, plain, (![A_112, B_113, C_114]: (k2_relset_1(A_112, B_113, C_114)=k2_relat_1(C_114) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_112, B_113))))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.65/4.11  tff(c_549, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_540])).
% 10.65/4.11  tff(c_554, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_549])).
% 10.65/4.11  tff(c_44, plain, (![A_32]: (k5_relat_1(k2_funct_1(A_32), A_32)=k6_relat_1(k2_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.65/4.11  tff(c_94, plain, (![A_32]: (k5_relat_1(k2_funct_1(A_32), A_32)=k6_partfun1(k2_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_44])).
% 10.65/4.11  tff(c_18, plain, (![A_11, B_13]: (r1_tarski(k2_relat_1(k5_relat_1(A_11, B_13)), k2_relat_1(B_13)) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.65/4.11  tff(c_650, plain, (![A_119]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_119, '#skF_3'))), k2_relat_1(k4_relat_1(A_119))) | ~v1_relat_1(k4_relat_1(A_119)) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(A_119))), inference(superposition, [status(thm), theory('equality')], [c_644, c_18])).
% 10.65/4.11  tff(c_1158, plain, (![A_131]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(A_131, '#skF_3'))), k2_relat_1(k4_relat_1(A_131))) | ~v1_relat_1(k4_relat_1(A_131)) | ~v1_relat_1(A_131))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_650])).
% 10.65/4.11  tff(c_1179, plain, (r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(k2_relat_1('#skF_3')))), k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_94, c_1158])).
% 10.65/4.11  tff(c_1206, plain, (r1_tarski('#skF_2', k2_relat_1(k4_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_92, c_76, c_280, c_554, c_98, c_97, c_1179])).
% 10.65/4.11  tff(c_1285, plain, (~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_1206])).
% 10.65/4.11  tff(c_1419, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_1285])).
% 10.65/4.11  tff(c_1423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_280, c_1419])).
% 10.65/4.11  tff(c_1425, plain, (v1_relat_1(k4_relat_1(k2_funct_1('#skF_3')))), inference(splitRight, [status(thm)], [c_1206])).
% 10.65/4.11  tff(c_46, plain, (![A_32]: (k5_relat_1(A_32, k2_funct_1(A_32))=k6_relat_1(k1_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.65/4.11  tff(c_93, plain, (![A_32]: (k5_relat_1(A_32, k2_funct_1(A_32))=k6_partfun1(k1_relat_1(A_32)) | ~v2_funct_1(A_32) | ~v1_funct_1(A_32) | ~v1_relat_1(A_32))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_46])).
% 10.65/4.11  tff(c_685, plain, (![B_120]: (k5_relat_1(k4_relat_1(B_120), k2_funct_1('#skF_3'))=k4_relat_1(k5_relat_1('#skF_3', B_120)) | ~v1_relat_1(B_120))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_627])).
% 10.65/4.11  tff(c_691, plain, (![B_120]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3', B_120))), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k4_relat_1(B_120)) | ~v1_relat_1(B_120))), inference(superposition, [status(thm), theory('equality')], [c_685, c_18])).
% 10.65/4.11  tff(c_1429, plain, (![B_137]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3', B_137))), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k4_relat_1(B_137)) | ~v1_relat_1(B_137))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_691])).
% 10.65/4.11  tff(c_1438, plain, (r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1(k1_relat_1('#skF_3')))), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_93, c_1429])).
% 10.65/4.11  tff(c_1453, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_92, c_76, c_280, c_1425, c_98, c_97, c_1438])).
% 10.65/4.11  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.65/4.11  tff(c_1467, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_3')), k1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_1453, c_2])).
% 10.65/4.11  tff(c_1479, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_758, c_1467])).
% 10.65/4.11  tff(c_1504, plain, (![A_11]: (r1_tarski(k2_relat_1(k5_relat_1(A_11, k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_1479, c_18])).
% 10.65/4.11  tff(c_1737, plain, (![A_141]: (r1_tarski(k2_relat_1(k5_relat_1(A_141, k2_funct_1('#skF_3'))), k1_relat_1('#skF_3')) | ~v1_relat_1(A_141))), inference(demodulation, [status(thm), theory('equality')], [c_280, c_1504])).
% 10.65/4.11  tff(c_1757, plain, (![B_117]: (r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1('#skF_3', B_117))), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1(B_117)) | ~v1_relat_1(B_117))), inference(superposition, [status(thm), theory('equality')], [c_639, c_1737])).
% 10.65/4.11  tff(c_7102, plain, (r1_tarski(k2_relat_1(k4_relat_1(k6_partfun1('#skF_1'))), k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7098, c_1757])).
% 10.65/4.11  tff(c_7112, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1(k4_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_166, c_98, c_97, c_7102])).
% 10.65/4.11  tff(c_7125, plain, (~v1_relat_1(k4_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_7112])).
% 10.65/4.11  tff(c_7289, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_7125])).
% 10.65/4.11  tff(c_7293, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_166, c_7289])).
% 10.65/4.11  tff(c_7294, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_7112])).
% 10.65/4.11  tff(c_217, plain, (![B_83, A_84]: (r1_tarski(k1_relat_1(B_83), A_84) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.65/4.11  tff(c_223, plain, (![B_83, A_84]: (k1_relat_1(B_83)=A_84 | ~r1_tarski(A_84, k1_relat_1(B_83)) | ~v4_relat_1(B_83, A_84) | ~v1_relat_1(B_83))), inference(resolution, [status(thm)], [c_217, c_2])).
% 10.65/4.11  tff(c_7298, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7294, c_223])).
% 10.65/4.11  tff(c_7308, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_216, c_7298])).
% 10.65/4.11  tff(c_96, plain, (![A_26, B_27]: (k5_relat_1(k6_partfun1(A_26), B_27)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_30])).
% 10.65/4.11  tff(c_1462, plain, (k5_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1453, c_96])).
% 10.65/4.11  tff(c_1473, plain, (k5_relat_1(k6_partfun1(k2_relat_1(k2_funct_1('#skF_3'))), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_169, c_1462])).
% 10.65/4.11  tff(c_1527, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1479, c_1473])).
% 10.65/4.11  tff(c_7328, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7308, c_1527])).
% 10.65/4.11  tff(c_667, plain, (![A_25]: (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1(A_25))=k4_relat_1(k5_relat_1(k6_partfun1(A_25), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_659])).
% 10.65/4.11  tff(c_1601, plain, (![A_138, B_139, C_140]: (k5_relat_1(k5_relat_1(A_138, B_139), C_140)=k5_relat_1(A_138, k5_relat_1(B_139, C_140)) | ~v1_relat_1(C_140) | ~v1_relat_1(B_139) | ~v1_relat_1(A_138))), inference(cnfTransformation, [status(thm)], [f_74])).
% 10.65/4.11  tff(c_11922, plain, (![A_481, C_482]: (k5_relat_1(k6_partfun1(k2_relat_1(A_481)), C_482)=k5_relat_1(k2_funct_1(A_481), k5_relat_1(A_481, C_482)) | ~v1_relat_1(C_482) | ~v1_relat_1(A_481) | ~v1_relat_1(k2_funct_1(A_481)) | ~v2_funct_1(A_481) | ~v1_funct_1(A_481) | ~v1_relat_1(A_481))), inference(superposition, [status(thm), theory('equality')], [c_94, c_1601])).
% 10.65/4.11  tff(c_12271, plain, (![C_482]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_482))=k5_relat_1(k6_partfun1('#skF_2'), C_482) | ~v1_relat_1(C_482) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_554, c_11922])).
% 10.65/4.11  tff(c_15210, plain, (![C_539]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_539))=k5_relat_1(k6_partfun1('#skF_2'), C_539) | ~v1_relat_1(C_539))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_92, c_76, c_280, c_169, c_12271])).
% 10.65/4.11  tff(c_15286, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7098, c_15210])).
% 10.65/4.11  tff(c_15343, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_166, c_272, c_7328, c_667, c_15286])).
% 10.65/4.11  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.65/4.11  tff(c_293, plain, (![A_6, B_7]: (k5_relat_1(k6_partfun1(A_6), B_7)=B_7 | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_282])).
% 10.65/4.11  tff(c_15991, plain, (k2_funct_1('#skF_3')='#skF_4' | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15343, c_293])).
% 10.65/4.12  tff(c_16018, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_166, c_215, c_15991])).
% 10.65/4.12  tff(c_16020, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_16018])).
% 10.65/4.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.65/4.12  
% 10.65/4.12  Inference rules
% 10.65/4.12  ----------------------
% 10.65/4.12  #Ref     : 0
% 10.65/4.12  #Sup     : 3325
% 10.65/4.12  #Fact    : 0
% 10.65/4.12  #Define  : 0
% 10.65/4.12  #Split   : 12
% 10.65/4.12  #Chain   : 0
% 10.65/4.12  #Close   : 0
% 10.65/4.12  
% 10.65/4.12  Ordering : KBO
% 10.65/4.12  
% 10.65/4.12  Simplification rules
% 10.65/4.12  ----------------------
% 10.65/4.12  #Subsume      : 179
% 10.65/4.12  #Demod        : 6010
% 10.65/4.12  #Tautology    : 1312
% 10.65/4.12  #SimpNegUnit  : 2
% 10.65/4.12  #BackRed      : 49
% 10.65/4.12  
% 10.65/4.12  #Partial instantiations: 0
% 10.65/4.12  #Strategies tried      : 1
% 10.65/4.12  
% 10.65/4.12  Timing (in seconds)
% 10.65/4.12  ----------------------
% 10.65/4.12  Preprocessing        : 0.37
% 10.65/4.12  Parsing              : 0.20
% 10.65/4.12  CNF conversion       : 0.03
% 10.65/4.12  Main loop            : 2.96
% 10.65/4.12  Inferencing          : 0.80
% 10.65/4.12  Reduction            : 1.41
% 10.65/4.12  Demodulation         : 1.17
% 10.65/4.12  BG Simplification    : 0.09
% 10.65/4.12  Subsumption          : 0.51
% 10.65/4.12  Abstraction          : 0.12
% 10.65/4.12  MUC search           : 0.00
% 10.65/4.12  Cooper               : 0.00
% 10.65/4.12  Total                : 3.38
% 10.65/4.12  Index Insertion      : 0.00
% 10.65/4.12  Index Deletion       : 0.00
% 10.65/4.12  Index Matching       : 0.00
% 10.65/4.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
