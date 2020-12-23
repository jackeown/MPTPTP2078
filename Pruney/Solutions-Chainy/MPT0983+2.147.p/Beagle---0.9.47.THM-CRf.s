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
% DateTime   : Thu Dec  3 10:12:22 EST 2020

% Result     : Theorem 7.51s
% Output     : CNFRefutation 7.51s
% Verified   : 
% Statistics : Number of formulae       :  151 ( 398 expanded)
%              Number of leaves         :   50 ( 158 expanded)
%              Depth                    :   15
%              Number of atoms          :  287 (1161 expanded)
%              Number of equality atoms :   50 ( 107 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_180,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
             => ( v2_funct_1(C)
                & v2_funct_2(D,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_funct_2)).

tff(f_57,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_83,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_102,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k1_relat_1(k5_relat_1(A,B)),k1_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_88,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_160,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_84,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_110,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_68,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_142,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_22,plain,(
    ! [A_11,B_12] : v1_relat_1(k2_zfmisc_1(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_78,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_261,plain,(
    ! [B_70,A_71] :
      ( v1_relat_1(B_70)
      | ~ m1_subset_1(B_70,k1_zfmisc_1(A_71))
      | ~ v1_relat_1(A_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_273,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_261])).

tff(c_285,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_273])).

tff(c_330,plain,(
    ! [C_82,A_83,B_84] :
      ( v4_relat_1(C_82,A_83)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_83,B_84))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_346,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_78,c_330])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_270,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_261])).

tff(c_282,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_270])).

tff(c_62,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_30,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_86,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_30])).

tff(c_82,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_3251,plain,(
    ! [C_342,E_339,B_338,D_337,F_341,A_340] :
      ( m1_subset_1(k1_partfun1(A_340,B_338,C_342,D_337,E_339,F_341),k1_zfmisc_1(k2_zfmisc_1(A_340,D_337)))
      | ~ m1_subset_1(F_341,k1_zfmisc_1(k2_zfmisc_1(C_342,D_337)))
      | ~ v1_funct_1(F_341)
      | ~ m1_subset_1(E_339,k1_zfmisc_1(k2_zfmisc_1(A_340,B_338)))
      | ~ v1_funct_1(E_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_58,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_2726,plain,(
    ! [D_292,C_293,A_294,B_295] :
      ( D_292 = C_293
      | ~ r2_relset_1(A_294,B_295,C_293,D_292)
      | ~ m1_subset_1(D_292,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ m1_subset_1(C_293,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_2736,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_2726])).

tff(c_2755,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2736])).

tff(c_2812,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_2755])).

tff(c_3254,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_3251,c_2812])).

tff(c_3279,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_3254])).

tff(c_3280,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_2755])).

tff(c_4299,plain,(
    ! [B_415,C_418,F_417,A_414,D_419,E_416] :
      ( k1_partfun1(A_414,B_415,C_418,D_419,E_416,F_417) = k5_relat_1(E_416,F_417)
      | ~ m1_subset_1(F_417,k1_zfmisc_1(k2_zfmisc_1(C_418,D_419)))
      | ~ v1_funct_1(F_417)
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415)))
      | ~ v1_funct_1(E_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_4307,plain,(
    ! [A_414,B_415,E_416] :
      ( k1_partfun1(A_414,B_415,'#skF_2','#skF_1',E_416,'#skF_4') = k5_relat_1(E_416,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_416,k1_zfmisc_1(k2_zfmisc_1(A_414,B_415)))
      | ~ v1_funct_1(E_416) ) ),
    inference(resolution,[status(thm)],[c_72,c_4299])).

tff(c_4534,plain,(
    ! [A_440,B_441,E_442] :
      ( k1_partfun1(A_440,B_441,'#skF_2','#skF_1',E_442,'#skF_4') = k5_relat_1(E_442,'#skF_4')
      | ~ m1_subset_1(E_442,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441)))
      | ~ v1_funct_1(E_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4307])).

tff(c_4552,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_4534])).

tff(c_4566,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_3280,c_4552])).

tff(c_26,plain,(
    ! [A_14,B_16] :
      ( r1_tarski(k1_relat_1(k5_relat_1(A_14,B_16)),k1_relat_1(A_14))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4576,plain,
    ( r1_tarski(k1_relat_1(k6_partfun1('#skF_1')),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4566,c_26])).

tff(c_4590,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_282,c_86,c_4576])).

tff(c_286,plain,(
    ! [B_72,A_73] :
      ( r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_295,plain,(
    ! [B_72,A_73] :
      ( k1_relat_1(B_72) = A_73
      | ~ r1_tarski(A_73,k1_relat_1(B_72))
      | ~ v4_relat_1(B_72,A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_286,c_6])).

tff(c_4598,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ v4_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4590,c_295])).

tff(c_4603,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_346,c_4598])).

tff(c_24,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4625,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4603,c_24])).

tff(c_4639,plain,
    ( ~ v1_xboole_0('#skF_1')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_4625])).

tff(c_4641,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4639])).

tff(c_80,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_38,plain,(
    ! [A_21] : v2_funct_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_83,plain,(
    ! [A_21] : v2_funct_1(k6_partfun1(A_21)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_38])).

tff(c_4724,plain,(
    ! [B_449,D_452,C_453,A_450,E_451] :
      ( k1_xboole_0 = C_453
      | v2_funct_1(D_452)
      | ~ v2_funct_1(k1_partfun1(A_450,B_449,B_449,C_453,D_452,E_451))
      | ~ m1_subset_1(E_451,k1_zfmisc_1(k2_zfmisc_1(B_449,C_453)))
      | ~ v1_funct_2(E_451,B_449,C_453)
      | ~ v1_funct_1(E_451)
      | ~ m1_subset_1(D_452,k1_zfmisc_1(k2_zfmisc_1(A_450,B_449)))
      | ~ v1_funct_2(D_452,A_450,B_449)
      | ~ v1_funct_1(D_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_4726,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3280,c_4724])).

tff(c_4728,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_78,c_76,c_74,c_72,c_83,c_4726])).

tff(c_4729,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_4728])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_4785,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4729,c_2])).

tff(c_4787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4641,c_4785])).

tff(c_4788,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_4639])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4797,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_4788,c_4])).

tff(c_102,plain,(
    ! [A_58] : k6_relat_1(A_58) = k6_partfun1(A_58) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_108,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_34])).

tff(c_121,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_83])).

tff(c_4864,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4797,c_121])).

tff(c_4873,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_4864])).

tff(c_4874,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_4994,plain,(
    ! [B_463,A_464] :
      ( v1_relat_1(B_463)
      | ~ m1_subset_1(B_463,k1_zfmisc_1(A_464))
      | ~ v1_relat_1(A_464) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5003,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_72,c_4994])).

tff(c_5015,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5003])).

tff(c_5279,plain,(
    ! [C_495,B_496,A_497] :
      ( v5_relat_1(C_495,B_496)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(A_497,B_496))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_5296,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_72,c_5279])).

tff(c_5006,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_78,c_4994])).

tff(c_5018,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_5006])).

tff(c_32,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_85,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_32])).

tff(c_5739,plain,(
    ! [D_549,A_544,F_547,C_548,E_546,B_545] :
      ( k1_partfun1(A_544,B_545,C_548,D_549,E_546,F_547) = k5_relat_1(E_546,F_547)
      | ~ m1_subset_1(F_547,k1_zfmisc_1(k2_zfmisc_1(C_548,D_549)))
      | ~ v1_funct_1(F_547)
      | ~ m1_subset_1(E_546,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545)))
      | ~ v1_funct_1(E_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_5745,plain,(
    ! [A_544,B_545,E_546] :
      ( k1_partfun1(A_544,B_545,'#skF_2','#skF_1',E_546,'#skF_4') = k5_relat_1(E_546,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_546,k1_zfmisc_1(k2_zfmisc_1(A_544,B_545)))
      | ~ v1_funct_1(E_546) ) ),
    inference(resolution,[status(thm)],[c_72,c_5739])).

tff(c_5976,plain,(
    ! [A_566,B_567,E_568] :
      ( k1_partfun1(A_566,B_567,'#skF_2','#skF_1',E_568,'#skF_4') = k5_relat_1(E_568,'#skF_4')
      | ~ m1_subset_1(E_568,k1_zfmisc_1(k2_zfmisc_1(A_566,B_567)))
      | ~ v1_funct_1(E_568) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5745])).

tff(c_5994,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_5976])).

tff(c_6004,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_5994])).

tff(c_52,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_6078,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6004,c_52])).

tff(c_6082,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_78,c_76,c_72,c_6078])).

tff(c_5534,plain,(
    ! [D_519,C_520,A_521,B_522] :
      ( D_519 = C_520
      | ~ r2_relset_1(A_521,B_522,C_520,D_519)
      | ~ m1_subset_1(D_519,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522)))
      | ~ m1_subset_1(C_520,k1_zfmisc_1(k2_zfmisc_1(A_521,B_522))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_5544,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_5534])).

tff(c_5563,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5544])).

tff(c_6484,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6082,c_6004,c_6004,c_5563])).

tff(c_28,plain,(
    ! [A_17,B_19] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_17,B_19)),k2_relat_1(B_19))
      | ~ v1_relat_1(B_19)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6503,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6484,c_28])).

tff(c_6510,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5018,c_5015,c_85,c_6503])).

tff(c_5137,plain,(
    ! [B_480,A_481] :
      ( r1_tarski(k2_relat_1(B_480),A_481)
      | ~ v5_relat_1(B_480,A_481)
      | ~ v1_relat_1(B_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5150,plain,(
    ! [B_480,A_481] :
      ( k2_relat_1(B_480) = A_481
      | ~ r1_tarski(A_481,k2_relat_1(B_480))
      | ~ v5_relat_1(B_480,A_481)
      | ~ v1_relat_1(B_480) ) ),
    inference(resolution,[status(thm)],[c_5137,c_6])).

tff(c_6516,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6510,c_5150])).

tff(c_6521,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_5296,c_6516])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_5044,plain,(
    ! [B_469,A_470] :
      ( v5_relat_1(B_469,A_470)
      | ~ r1_tarski(k2_relat_1(B_469),A_470)
      | ~ v1_relat_1(B_469) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_5059,plain,(
    ! [B_469] :
      ( v5_relat_1(B_469,k2_relat_1(B_469))
      | ~ v1_relat_1(B_469) ) ),
    inference(resolution,[status(thm)],[c_10,c_5044])).

tff(c_5298,plain,(
    ! [B_498] :
      ( v2_funct_2(B_498,k2_relat_1(B_498))
      | ~ v5_relat_1(B_498,k2_relat_1(B_498))
      | ~ v1_relat_1(B_498) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_5322,plain,(
    ! [B_469] :
      ( v2_funct_2(B_469,k2_relat_1(B_469))
      | ~ v1_relat_1(B_469) ) ),
    inference(resolution,[status(thm)],[c_5059,c_5298])).

tff(c_6534,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6521,c_5322])).

tff(c_6551,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_6534])).

tff(c_6553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4874,c_6551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:52:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.51/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.58  
% 7.51/2.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.59  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.51/2.59  
% 7.51/2.59  %Foreground sorts:
% 7.51/2.59  
% 7.51/2.59  
% 7.51/2.59  %Background operators:
% 7.51/2.59  
% 7.51/2.59  
% 7.51/2.59  %Foreground operators:
% 7.51/2.59  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.51/2.59  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.51/2.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.51/2.59  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.51/2.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.51/2.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.51/2.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.51/2.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.51/2.59  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.51/2.59  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.51/2.59  tff('#skF_2', type, '#skF_2': $i).
% 7.51/2.59  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.51/2.59  tff('#skF_3', type, '#skF_3': $i).
% 7.51/2.59  tff('#skF_1', type, '#skF_1': $i).
% 7.51/2.59  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.51/2.59  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.51/2.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.51/2.59  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.51/2.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.51/2.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.51/2.59  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.51/2.59  tff('#skF_4', type, '#skF_4': $i).
% 7.51/2.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.51/2.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.51/2.59  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.51/2.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.51/2.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.51/2.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.51/2.59  
% 7.51/2.62  tff(f_180, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.51/2.62  tff(f_57, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 7.51/2.62  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.51/2.62  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.51/2.62  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.51/2.62  tff(f_83, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 7.51/2.62  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.51/2.62  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.51/2.62  tff(f_102, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.51/2.62  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 7.51/2.62  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k5_relat_1(A, B)), k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_relat_1)).
% 7.51/2.62  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.51/2.62  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.51/2.62  tff(f_65, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc8_relat_1)).
% 7.51/2.62  tff(f_88, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.51/2.62  tff(f_160, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.51/2.62  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.51/2.62  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 7.51/2.62  tff(f_84, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 7.51/2.62  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 7.51/2.62  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.51/2.62  tff(f_110, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.51/2.62  tff(c_68, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_142, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_68])).
% 7.51/2.62  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k2_zfmisc_1(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 7.51/2.62  tff(c_78, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_261, plain, (![B_70, A_71]: (v1_relat_1(B_70) | ~m1_subset_1(B_70, k1_zfmisc_1(A_71)) | ~v1_relat_1(A_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.62  tff(c_273, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_261])).
% 7.51/2.62  tff(c_285, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_273])).
% 7.51/2.62  tff(c_330, plain, (![C_82, A_83, B_84]: (v4_relat_1(C_82, A_83) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_83, B_84))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.51/2.62  tff(c_346, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_78, c_330])).
% 7.51/2.62  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_270, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_261])).
% 7.51/2.62  tff(c_282, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_270])).
% 7.51/2.62  tff(c_62, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.51/2.62  tff(c_30, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.51/2.62  tff(c_86, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_30])).
% 7.51/2.62  tff(c_82, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_3251, plain, (![C_342, E_339, B_338, D_337, F_341, A_340]: (m1_subset_1(k1_partfun1(A_340, B_338, C_342, D_337, E_339, F_341), k1_zfmisc_1(k2_zfmisc_1(A_340, D_337))) | ~m1_subset_1(F_341, k1_zfmisc_1(k2_zfmisc_1(C_342, D_337))) | ~v1_funct_1(F_341) | ~m1_subset_1(E_339, k1_zfmisc_1(k2_zfmisc_1(A_340, B_338))) | ~v1_funct_1(E_339))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.51/2.62  tff(c_58, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.51/2.62  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_2726, plain, (![D_292, C_293, A_294, B_295]: (D_292=C_293 | ~r2_relset_1(A_294, B_295, C_293, D_292) | ~m1_subset_1(D_292, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~m1_subset_1(C_293, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.62  tff(c_2736, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_2726])).
% 7.51/2.62  tff(c_2755, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2736])).
% 7.51/2.62  tff(c_2812, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_2755])).
% 7.51/2.62  tff(c_3254, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_3251, c_2812])).
% 7.51/2.62  tff(c_3279, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_3254])).
% 7.51/2.62  tff(c_3280, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_2755])).
% 7.51/2.62  tff(c_4299, plain, (![B_415, C_418, F_417, A_414, D_419, E_416]: (k1_partfun1(A_414, B_415, C_418, D_419, E_416, F_417)=k5_relat_1(E_416, F_417) | ~m1_subset_1(F_417, k1_zfmisc_1(k2_zfmisc_1(C_418, D_419))) | ~v1_funct_1(F_417) | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))) | ~v1_funct_1(E_416))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.51/2.62  tff(c_4307, plain, (![A_414, B_415, E_416]: (k1_partfun1(A_414, B_415, '#skF_2', '#skF_1', E_416, '#skF_4')=k5_relat_1(E_416, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_416, k1_zfmisc_1(k2_zfmisc_1(A_414, B_415))) | ~v1_funct_1(E_416))), inference(resolution, [status(thm)], [c_72, c_4299])).
% 7.51/2.62  tff(c_4534, plain, (![A_440, B_441, E_442]: (k1_partfun1(A_440, B_441, '#skF_2', '#skF_1', E_442, '#skF_4')=k5_relat_1(E_442, '#skF_4') | ~m1_subset_1(E_442, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))) | ~v1_funct_1(E_442))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4307])).
% 7.51/2.62  tff(c_4552, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_4534])).
% 7.51/2.62  tff(c_4566, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_3280, c_4552])).
% 7.51/2.62  tff(c_26, plain, (![A_14, B_16]: (r1_tarski(k1_relat_1(k5_relat_1(A_14, B_16)), k1_relat_1(A_14)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.51/2.62  tff(c_4576, plain, (r1_tarski(k1_relat_1(k6_partfun1('#skF_1')), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4566, c_26])).
% 7.51/2.62  tff(c_4590, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_282, c_86, c_4576])).
% 7.51/2.62  tff(c_286, plain, (![B_72, A_73]: (r1_tarski(k1_relat_1(B_72), A_73) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.51/2.62  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.51/2.62  tff(c_295, plain, (![B_72, A_73]: (k1_relat_1(B_72)=A_73 | ~r1_tarski(A_73, k1_relat_1(B_72)) | ~v4_relat_1(B_72, A_73) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_286, c_6])).
% 7.51/2.62  tff(c_4598, plain, (k1_relat_1('#skF_3')='#skF_1' | ~v4_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4590, c_295])).
% 7.51/2.62  tff(c_4603, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_285, c_346, c_4598])).
% 7.51/2.62  tff(c_24, plain, (![A_13]: (~v1_xboole_0(k1_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.51/2.62  tff(c_4625, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_3') | v1_xboole_0('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4603, c_24])).
% 7.51/2.62  tff(c_4639, plain, (~v1_xboole_0('#skF_1') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_4625])).
% 7.51/2.62  tff(c_4641, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_4639])).
% 7.51/2.62  tff(c_80, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_180])).
% 7.51/2.62  tff(c_38, plain, (![A_21]: (v2_funct_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_88])).
% 7.51/2.62  tff(c_83, plain, (![A_21]: (v2_funct_1(k6_partfun1(A_21)))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_38])).
% 7.51/2.62  tff(c_4724, plain, (![B_449, D_452, C_453, A_450, E_451]: (k1_xboole_0=C_453 | v2_funct_1(D_452) | ~v2_funct_1(k1_partfun1(A_450, B_449, B_449, C_453, D_452, E_451)) | ~m1_subset_1(E_451, k1_zfmisc_1(k2_zfmisc_1(B_449, C_453))) | ~v1_funct_2(E_451, B_449, C_453) | ~v1_funct_1(E_451) | ~m1_subset_1(D_452, k1_zfmisc_1(k2_zfmisc_1(A_450, B_449))) | ~v1_funct_2(D_452, A_450, B_449) | ~v1_funct_1(D_452))), inference(cnfTransformation, [status(thm)], [f_160])).
% 7.51/2.62  tff(c_4726, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3280, c_4724])).
% 7.51/2.62  tff(c_4728, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_78, c_76, c_74, c_72, c_83, c_4726])).
% 7.51/2.62  tff(c_4729, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_142, c_4728])).
% 7.51/2.62  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.51/2.62  tff(c_4785, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4729, c_2])).
% 7.51/2.62  tff(c_4787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4641, c_4785])).
% 7.51/2.62  tff(c_4788, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_4639])).
% 7.51/2.62  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 7.51/2.62  tff(c_4797, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_4788, c_4])).
% 7.51/2.62  tff(c_102, plain, (![A_58]: (k6_relat_1(A_58)=k6_partfun1(A_58))), inference(cnfTransformation, [status(thm)], [f_138])).
% 7.51/2.62  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.51/2.62  tff(c_108, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_102, c_34])).
% 7.51/2.62  tff(c_121, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_108, c_83])).
% 7.51/2.62  tff(c_4864, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4797, c_121])).
% 7.51/2.62  tff(c_4873, plain, $false, inference(negUnitSimplification, [status(thm)], [c_142, c_4864])).
% 7.51/2.62  tff(c_4874, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_68])).
% 7.51/2.62  tff(c_4994, plain, (![B_463, A_464]: (v1_relat_1(B_463) | ~m1_subset_1(B_463, k1_zfmisc_1(A_464)) | ~v1_relat_1(A_464))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.51/2.62  tff(c_5003, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_72, c_4994])).
% 7.51/2.62  tff(c_5015, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5003])).
% 7.51/2.62  tff(c_5279, plain, (![C_495, B_496, A_497]: (v5_relat_1(C_495, B_496) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(A_497, B_496))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.51/2.62  tff(c_5296, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_72, c_5279])).
% 7.51/2.62  tff(c_5006, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_78, c_4994])).
% 7.51/2.62  tff(c_5018, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_5006])).
% 7.51/2.62  tff(c_32, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_83])).
% 7.51/2.62  tff(c_85, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_62, c_32])).
% 7.51/2.62  tff(c_5739, plain, (![D_549, A_544, F_547, C_548, E_546, B_545]: (k1_partfun1(A_544, B_545, C_548, D_549, E_546, F_547)=k5_relat_1(E_546, F_547) | ~m1_subset_1(F_547, k1_zfmisc_1(k2_zfmisc_1(C_548, D_549))) | ~v1_funct_1(F_547) | ~m1_subset_1(E_546, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))) | ~v1_funct_1(E_546))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.51/2.62  tff(c_5745, plain, (![A_544, B_545, E_546]: (k1_partfun1(A_544, B_545, '#skF_2', '#skF_1', E_546, '#skF_4')=k5_relat_1(E_546, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_546, k1_zfmisc_1(k2_zfmisc_1(A_544, B_545))) | ~v1_funct_1(E_546))), inference(resolution, [status(thm)], [c_72, c_5739])).
% 7.51/2.62  tff(c_5976, plain, (![A_566, B_567, E_568]: (k1_partfun1(A_566, B_567, '#skF_2', '#skF_1', E_568, '#skF_4')=k5_relat_1(E_568, '#skF_4') | ~m1_subset_1(E_568, k1_zfmisc_1(k2_zfmisc_1(A_566, B_567))) | ~v1_funct_1(E_568))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5745])).
% 7.51/2.62  tff(c_5994, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_5976])).
% 7.51/2.62  tff(c_6004, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_5994])).
% 7.51/2.62  tff(c_52, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_122])).
% 7.51/2.62  tff(c_6078, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6004, c_52])).
% 7.51/2.62  tff(c_6082, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_78, c_76, c_72, c_6078])).
% 7.51/2.62  tff(c_5534, plain, (![D_519, C_520, A_521, B_522]: (D_519=C_520 | ~r2_relset_1(A_521, B_522, C_520, D_519) | ~m1_subset_1(D_519, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))) | ~m1_subset_1(C_520, k1_zfmisc_1(k2_zfmisc_1(A_521, B_522))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.51/2.62  tff(c_5544, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_5534])).
% 7.51/2.62  tff(c_5563, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_5544])).
% 7.51/2.62  tff(c_6484, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6082, c_6004, c_6004, c_5563])).
% 7.51/2.62  tff(c_28, plain, (![A_17, B_19]: (r1_tarski(k2_relat_1(k5_relat_1(A_17, B_19)), k2_relat_1(B_19)) | ~v1_relat_1(B_19) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_79])).
% 7.51/2.62  tff(c_6503, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6484, c_28])).
% 7.51/2.62  tff(c_6510, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5018, c_5015, c_85, c_6503])).
% 7.51/2.62  tff(c_5137, plain, (![B_480, A_481]: (r1_tarski(k2_relat_1(B_480), A_481) | ~v5_relat_1(B_480, A_481) | ~v1_relat_1(B_480))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.51/2.62  tff(c_5150, plain, (![B_480, A_481]: (k2_relat_1(B_480)=A_481 | ~r1_tarski(A_481, k2_relat_1(B_480)) | ~v5_relat_1(B_480, A_481) | ~v1_relat_1(B_480))), inference(resolution, [status(thm)], [c_5137, c_6])).
% 7.51/2.62  tff(c_6516, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6510, c_5150])).
% 7.51/2.62  tff(c_6521, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_5296, c_6516])).
% 7.51/2.62  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 7.51/2.62  tff(c_5044, plain, (![B_469, A_470]: (v5_relat_1(B_469, A_470) | ~r1_tarski(k2_relat_1(B_469), A_470) | ~v1_relat_1(B_469))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.51/2.62  tff(c_5059, plain, (![B_469]: (v5_relat_1(B_469, k2_relat_1(B_469)) | ~v1_relat_1(B_469))), inference(resolution, [status(thm)], [c_10, c_5044])).
% 7.51/2.62  tff(c_5298, plain, (![B_498]: (v2_funct_2(B_498, k2_relat_1(B_498)) | ~v5_relat_1(B_498, k2_relat_1(B_498)) | ~v1_relat_1(B_498))), inference(cnfTransformation, [status(thm)], [f_110])).
% 7.51/2.62  tff(c_5322, plain, (![B_469]: (v2_funct_2(B_469, k2_relat_1(B_469)) | ~v1_relat_1(B_469))), inference(resolution, [status(thm)], [c_5059, c_5298])).
% 7.51/2.62  tff(c_6534, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6521, c_5322])).
% 7.51/2.62  tff(c_6551, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5015, c_6534])).
% 7.51/2.62  tff(c_6553, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4874, c_6551])).
% 7.51/2.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.51/2.62  
% 7.51/2.62  Inference rules
% 7.51/2.62  ----------------------
% 7.51/2.62  #Ref     : 0
% 7.51/2.62  #Sup     : 1323
% 7.51/2.62  #Fact    : 0
% 7.51/2.62  #Define  : 0
% 7.51/2.62  #Split   : 27
% 7.51/2.62  #Chain   : 0
% 7.51/2.62  #Close   : 0
% 7.51/2.62  
% 7.51/2.62  Ordering : KBO
% 7.51/2.62  
% 7.51/2.62  Simplification rules
% 7.51/2.62  ----------------------
% 7.51/2.62  #Subsume      : 339
% 7.51/2.62  #Demod        : 1546
% 7.51/2.62  #Tautology    : 387
% 7.51/2.62  #SimpNegUnit  : 32
% 7.51/2.62  #BackRed      : 253
% 7.51/2.62  
% 7.51/2.62  #Partial instantiations: 0
% 7.51/2.62  #Strategies tried      : 1
% 7.51/2.62  
% 7.51/2.62  Timing (in seconds)
% 7.51/2.62  ----------------------
% 7.51/2.62  Preprocessing        : 0.35
% 7.51/2.62  Parsing              : 0.19
% 7.51/2.62  CNF conversion       : 0.02
% 7.51/2.62  Main loop            : 1.47
% 7.51/2.62  Inferencing          : 0.48
% 7.51/2.62  Reduction            : 0.53
% 7.51/2.62  Demodulation         : 0.39
% 7.51/2.62  BG Simplification    : 0.05
% 7.51/2.62  Subsumption          : 0.29
% 7.51/2.62  Abstraction          : 0.06
% 7.51/2.62  MUC search           : 0.00
% 7.51/2.62  Cooper               : 0.00
% 7.51/2.62  Total                : 1.89
% 7.51/2.62  Index Insertion      : 0.00
% 7.51/2.63  Index Deletion       : 0.00
% 7.51/2.63  Index Matching       : 0.00
% 7.51/2.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
