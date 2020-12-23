%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:11 EST 2020

% Result     : Theorem 7.15s
% Output     : CNFRefutation 7.31s
% Verified   : 
% Statistics : Number of formulae       :  204 (1462 expanded)
%              Number of leaves         :   47 ( 499 expanded)
%              Depth                    :   13
%              Number of atoms          :  375 (4274 expanded)
%              Number of equality atoms :   84 ( 917 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_167,negated_conjecture,(
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

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_108,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_106,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_147,axiom,(
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

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & v1_funct_2(D,B,A)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
         => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
           => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_64,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_94,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_72,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_70,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_68,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_56,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_30,plain,(
    ! [A_15] : v2_funct_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_79,plain,(
    ! [A_15] : v2_funct_1(k6_partfun1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_30])).

tff(c_48,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_54,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_66,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_167])).

tff(c_1895,plain,(
    ! [D_320,C_321,A_322,B_323] :
      ( D_320 = C_321
      | ~ r2_relset_1(A_322,B_323,C_321,D_320)
      | ~ m1_subset_1(D_320,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323)))
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_322,B_323))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1905,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_1895])).

tff(c_1924,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1905])).

tff(c_2250,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_1924])).

tff(c_2359,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_2250])).

tff(c_2366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_2359])).

tff(c_2367,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_2416,plain,(
    ! [C_401,E_403,B_402,A_404,D_400] :
      ( k1_xboole_0 = C_401
      | v2_funct_1(D_400)
      | ~ v2_funct_1(k1_partfun1(A_404,B_402,B_402,C_401,D_400,E_403))
      | ~ m1_subset_1(E_403,k1_zfmisc_1(k2_zfmisc_1(B_402,C_401)))
      | ~ v1_funct_2(E_403,B_402,C_401)
      | ~ v1_funct_1(E_403)
      | ~ m1_subset_1(D_400,k1_zfmisc_1(k2_zfmisc_1(A_404,B_402)))
      | ~ v1_funct_2(D_400,A_404,B_402)
      | ~ v1_funct_1(D_400) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2418,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2367,c_2416])).

tff(c_2420,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_68,c_79,c_2418])).

tff(c_2421,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_2420])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2455,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_8])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2454,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2421,c_2421,c_18])).

tff(c_936,plain,(
    ! [C_175,B_176,A_177] :
      ( ~ v1_xboole_0(C_175)
      | ~ m1_subset_1(B_176,k1_zfmisc_1(C_175))
      | ~ r2_hidden(A_177,B_176) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_952,plain,(
    ! [A_177] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_177,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_68,c_936])).

tff(c_960,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_952])).

tff(c_2608,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2454,c_960])).

tff(c_2614,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2455,c_2608])).

tff(c_2616,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_952])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_3215,plain,(
    ! [B_483,A_484,A_485] :
      ( ~ v1_xboole_0(B_483)
      | ~ r2_hidden(A_484,A_485)
      | ~ r1_tarski(A_485,B_483) ) ),
    inference(resolution,[status(thm)],[c_24,c_936])).

tff(c_3275,plain,(
    ! [B_497,A_498,B_499] :
      ( ~ v1_xboole_0(B_497)
      | ~ r1_tarski(A_498,B_497)
      | r1_tarski(A_498,B_499) ) ),
    inference(resolution,[status(thm)],[c_6,c_3215])).

tff(c_3289,plain,(
    ! [B_500,B_501] :
      ( ~ v1_xboole_0(B_500)
      | r1_tarski(B_500,B_501) ) ),
    inference(resolution,[status(thm)],[c_14,c_3275])).

tff(c_120,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_127,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_164,plain,(
    ! [B_66,A_67] :
      ( B_66 = A_67
      | ~ r1_tarski(B_66,A_67)
      | ~ r1_tarski(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_178,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_127,c_164])).

tff(c_828,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_3317,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_3289,c_828])).

tff(c_3330,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2616,c_3317])).

tff(c_3331,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_3335,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_68])).

tff(c_3958,plain,(
    ! [D_591,C_592,A_593,B_594] :
      ( D_591 = C_592
      | ~ r2_relset_1(A_593,B_594,C_592,D_591)
      | ~ m1_subset_1(D_591,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594)))
      | ~ m1_subset_1(C_592,k1_zfmisc_1(k2_zfmisc_1(A_593,B_594))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3968,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_3958])).

tff(c_3987,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_3968])).

tff(c_4009,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_3987])).

tff(c_4259,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_4009])).

tff(c_4266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_3335,c_3331,c_4259])).

tff(c_4267,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3987])).

tff(c_4651,plain,(
    ! [C_702,A_705,B_703,E_704,D_701] :
      ( k1_xboole_0 = C_702
      | v2_funct_1(D_701)
      | ~ v2_funct_1(k1_partfun1(A_705,B_703,B_703,C_702,D_701,E_704))
      | ~ m1_subset_1(E_704,k1_zfmisc_1(k2_zfmisc_1(B_703,C_702)))
      | ~ v1_funct_2(E_704,B_703,C_702)
      | ~ v1_funct_1(E_704)
      | ~ m1_subset_1(D_701,k1_zfmisc_1(k2_zfmisc_1(A_705,B_703)))
      | ~ v1_funct_2(D_701,A_705,B_703)
      | ~ v1_funct_1(D_701) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_4653,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4267,c_4651])).

tff(c_4655,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_72,c_70,c_3335,c_3331,c_79,c_4653])).

tff(c_4656,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_4655])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3340,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3331,c_16])).

tff(c_3359,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3340])).

tff(c_4688,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4656,c_3359])).

tff(c_4696,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4656,c_4656,c_18])).

tff(c_4875,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4696,c_3331])).

tff(c_4877,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4688,c_4875])).

tff(c_4879,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3340])).

tff(c_4878,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3340])).

tff(c_4894,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4879,c_4879,c_4878])).

tff(c_4895,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4894])).

tff(c_4888,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4879,c_8])).

tff(c_4896,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4888])).

tff(c_4898,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4895,c_3335])).

tff(c_26,plain,(
    ! [C_14,B_13,A_12] :
      ( ~ v1_xboole_0(C_14)
      | ~ m1_subset_1(B_13,k1_zfmisc_1(C_14))
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_5034,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_12,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_4898,c_26])).

tff(c_5043,plain,(
    ! [A_731] : ~ r2_hidden(A_731,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4896,c_5034])).

tff(c_5048,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_5043])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4886,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4879,c_4879,c_20])).

tff(c_4950,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4895,c_4895,c_4886])).

tff(c_128,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_74,c_120])).

tff(c_177,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_128,c_164])).

tff(c_3333,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_4951,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4950,c_3333])).

tff(c_5051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5048,c_4951])).

tff(c_5052,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4894])).

tff(c_5054,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_4888])).

tff(c_5056,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_5052,c_3335])).

tff(c_5217,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_12,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_5056,c_26])).

tff(c_5226,plain,(
    ! [A_746] : ~ r2_hidden(A_746,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5054,c_5217])).

tff(c_5231,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_5226])).

tff(c_4887,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4879,c_4879,c_18])).

tff(c_5119,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5052,c_5052,c_4887])).

tff(c_5120,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5119,c_3333])).

tff(c_5234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5231,c_5120])).

tff(c_5235,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_5248,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_74])).

tff(c_5238,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3331,c_68])).

tff(c_5900,plain,(
    ! [D_836,C_837,A_838,B_839] :
      ( D_836 = C_837
      | ~ r2_relset_1(A_838,B_839,C_837,D_836)
      | ~ m1_subset_1(D_836,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839)))
      | ~ m1_subset_1(C_837,k1_zfmisc_1(k2_zfmisc_1(A_838,B_839))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_5908,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_5900])).

tff(c_5923,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_5908])).

tff(c_6033,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5923])).

tff(c_6145,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_6033])).

tff(c_6152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5248,c_5235,c_72,c_5238,c_3331,c_6145])).

tff(c_6153,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5923])).

tff(c_6445,plain,(
    ! [C_927,B_928,D_926,A_930,E_929] :
      ( k1_xboole_0 = C_927
      | v2_funct_1(D_926)
      | ~ v2_funct_1(k1_partfun1(A_930,B_928,B_928,C_927,D_926,E_929))
      | ~ m1_subset_1(E_929,k1_zfmisc_1(k2_zfmisc_1(B_928,C_927)))
      | ~ v1_funct_2(E_929,B_928,C_927)
      | ~ v1_funct_1(E_929)
      | ~ m1_subset_1(D_926,k1_zfmisc_1(k2_zfmisc_1(A_930,B_928)))
      | ~ v1_funct_2(D_926,A_930,B_928)
      | ~ v1_funct_1(D_926) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_6447,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6153,c_6445])).

tff(c_6449,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_5248,c_5235,c_72,c_70,c_5238,c_3331,c_79,c_6447])).

tff(c_6450,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6449])).

tff(c_5253,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5235,c_16])).

tff(c_5279,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5253])).

tff(c_6481,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6450,c_5279])).

tff(c_6657,plain,(
    ! [B_943] : k2_zfmisc_1('#skF_2',B_943) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6450,c_6450,c_20])).

tff(c_6713,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6657,c_5235])).

tff(c_6740,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6481,c_6713])).

tff(c_6742,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5253])).

tff(c_306,plain,(
    ! [C_86,B_87,A_88] :
      ( ~ v1_xboole_0(C_86)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(C_86))
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_376,plain,(
    ! [B_100,A_101,A_102] :
      ( ~ v1_xboole_0(B_100)
      | ~ r2_hidden(A_101,A_102)
      | ~ r1_tarski(A_102,B_100) ) ),
    inference(resolution,[status(thm)],[c_24,c_306])).

tff(c_725,plain,(
    ! [B_153,A_154,B_155] :
      ( ~ v1_xboole_0(B_153)
      | ~ r1_tarski(A_154,B_153)
      | r1_tarski(A_154,B_155) ) ),
    inference(resolution,[status(thm)],[c_6,c_376])).

tff(c_742,plain,(
    ! [B_156,B_157] :
      ( ~ v1_xboole_0(B_156)
      | r1_tarski(B_156,B_157) ) ),
    inference(resolution,[status(thm)],[c_14,c_725])).

tff(c_134,plain,(
    ! [A_62] : m1_subset_1(k6_partfun1(A_62),k1_zfmisc_1(k2_zfmisc_1(A_62,A_62))) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_141,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_134])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_150,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_141,c_22])).

tff(c_176,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_150,c_164])).

tff(c_183,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_773,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_742,c_183])).

tff(c_787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_773])).

tff(c_788,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_806,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_79])).

tff(c_6746,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6742,c_806])).

tff(c_6755,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_6746])).

tff(c_6756,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_6827,plain,(
    ! [C_955,A_956,B_957] :
      ( v1_relat_1(C_955)
      | ~ m1_subset_1(C_955,k1_zfmisc_1(k2_zfmisc_1(A_956,B_957))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6848,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_6827])).

tff(c_7509,plain,(
    ! [C_1051,B_1052,A_1053] :
      ( v5_relat_1(C_1051,B_1052)
      | ~ m1_subset_1(C_1051,k1_zfmisc_1(k2_zfmisc_1(A_1053,B_1052))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_7531,plain,(
    v5_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_7509])).

tff(c_7717,plain,(
    ! [A_1089,B_1090,D_1091] :
      ( r2_relset_1(A_1089,B_1090,D_1091,D_1091)
      | ~ m1_subset_1(D_1091,k1_zfmisc_1(k2_zfmisc_1(A_1089,B_1090))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7732,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_54,c_7717])).

tff(c_7786,plain,(
    ! [A_1096,B_1097,C_1098] :
      ( k2_relset_1(A_1096,B_1097,C_1098) = k2_relat_1(C_1098)
      | ~ m1_subset_1(C_1098,k1_zfmisc_1(k2_zfmisc_1(A_1096,B_1097))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_7808,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_68,c_7786])).

tff(c_7819,plain,(
    ! [D_1099,C_1100,A_1101,B_1102] :
      ( D_1099 = C_1100
      | ~ r2_relset_1(A_1101,B_1102,C_1100,D_1099)
      | ~ m1_subset_1(D_1099,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1102)))
      | ~ m1_subset_1(C_1100,k1_zfmisc_1(k2_zfmisc_1(A_1101,B_1102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_7829,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_66,c_7819])).

tff(c_7848,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_7829])).

tff(c_8198,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_7848])).

tff(c_8299,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_48,c_8198])).

tff(c_8306,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_74,c_72,c_68,c_8299])).

tff(c_8307,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_7848])).

tff(c_8439,plain,(
    ! [A_1202,B_1203,C_1204,D_1205] :
      ( k2_relset_1(A_1202,B_1203,C_1204) = B_1203
      | ~ r2_relset_1(B_1203,B_1203,k1_partfun1(B_1203,A_1202,A_1202,B_1203,D_1205,C_1204),k6_partfun1(B_1203))
      | ~ m1_subset_1(D_1205,k1_zfmisc_1(k2_zfmisc_1(B_1203,A_1202)))
      | ~ v1_funct_2(D_1205,B_1203,A_1202)
      | ~ v1_funct_1(D_1205)
      | ~ m1_subset_1(C_1204,k1_zfmisc_1(k2_zfmisc_1(A_1202,B_1203)))
      | ~ v1_funct_2(C_1204,A_1202,B_1203)
      | ~ v1_funct_1(C_1204) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_8442,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8307,c_8439])).

tff(c_8447,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_78,c_76,c_74,c_7732,c_7808,c_8442])).

tff(c_44,plain,(
    ! [B_30] :
      ( v2_funct_2(B_30,k2_relat_1(B_30))
      | ~ v5_relat_1(B_30,k2_relat_1(B_30))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8459,plain,
    ( v2_funct_2('#skF_5',k2_relat_1('#skF_5'))
    | ~ v5_relat_1('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_8447,c_44])).

tff(c_8469,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6848,c_7531,c_8447,c_8459])).

tff(c_8471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6756,c_8469])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:54:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.15/2.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.68  
% 7.31/2.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.68  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.31/2.68  
% 7.31/2.68  %Foreground sorts:
% 7.31/2.68  
% 7.31/2.68  
% 7.31/2.68  %Background operators:
% 7.31/2.68  
% 7.31/2.68  
% 7.31/2.68  %Foreground operators:
% 7.31/2.68  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.31/2.68  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.31/2.68  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.31/2.68  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.31/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.31/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.31/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.31/2.68  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.31/2.68  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.31/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.31/2.68  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.31/2.68  tff('#skF_2', type, '#skF_2': $i).
% 7.31/2.68  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.31/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.31/2.68  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.31/2.68  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.31/2.68  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.31/2.68  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.31/2.68  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.31/2.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.31/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.31/2.68  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.31/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.31/2.68  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.31/2.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.31/2.68  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.31/2.68  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.31/2.68  
% 7.31/2.71  tff(f_167, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 7.31/2.71  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 7.31/2.71  tff(f_108, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 7.31/2.71  tff(f_60, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 7.31/2.71  tff(f_102, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 7.31/2.71  tff(f_106, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.31/2.71  tff(f_82, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 7.31/2.71  tff(f_147, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 7.31/2.71  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.31/2.71  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.31/2.71  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 7.31/2.71  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.31/2.71  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.31/2.71  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.31/2.71  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.31/2.71  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 7.31/2.71  tff(f_125, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 7.31/2.71  tff(f_90, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 7.31/2.71  tff(c_64, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_94, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_64])).
% 7.31/2.71  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.31/2.71  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_72, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_70, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_68, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_56, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_108])).
% 7.31/2.71  tff(c_30, plain, (![A_15]: (v2_funct_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 7.31/2.71  tff(c_79, plain, (![A_15]: (v2_funct_1(k6_partfun1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_30])).
% 7.31/2.71  tff(c_48, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_102])).
% 7.31/2.71  tff(c_54, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.31/2.71  tff(c_66, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_167])).
% 7.31/2.71  tff(c_1895, plain, (![D_320, C_321, A_322, B_323]: (D_320=C_321 | ~r2_relset_1(A_322, B_323, C_321, D_320) | ~m1_subset_1(D_320, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_322, B_323))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.31/2.71  tff(c_1905, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_1895])).
% 7.31/2.71  tff(c_1924, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1905])).
% 7.31/2.71  tff(c_2250, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_1924])).
% 7.31/2.71  tff(c_2359, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_2250])).
% 7.31/2.71  tff(c_2366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_2359])).
% 7.31/2.71  tff(c_2367, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_1924])).
% 7.31/2.71  tff(c_2416, plain, (![C_401, E_403, B_402, A_404, D_400]: (k1_xboole_0=C_401 | v2_funct_1(D_400) | ~v2_funct_1(k1_partfun1(A_404, B_402, B_402, C_401, D_400, E_403)) | ~m1_subset_1(E_403, k1_zfmisc_1(k2_zfmisc_1(B_402, C_401))) | ~v1_funct_2(E_403, B_402, C_401) | ~v1_funct_1(E_403) | ~m1_subset_1(D_400, k1_zfmisc_1(k2_zfmisc_1(A_404, B_402))) | ~v1_funct_2(D_400, A_404, B_402) | ~v1_funct_1(D_400))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.31/2.71  tff(c_2418, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2367, c_2416])).
% 7.31/2.71  tff(c_2420, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_68, c_79, c_2418])).
% 7.31/2.71  tff(c_2421, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_2420])).
% 7.31/2.71  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.31/2.71  tff(c_2455, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_8])).
% 7.31/2.71  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.71  tff(c_2454, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2421, c_2421, c_18])).
% 7.31/2.71  tff(c_936, plain, (![C_175, B_176, A_177]: (~v1_xboole_0(C_175) | ~m1_subset_1(B_176, k1_zfmisc_1(C_175)) | ~r2_hidden(A_177, B_176))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.71  tff(c_952, plain, (![A_177]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_177, '#skF_5'))), inference(resolution, [status(thm)], [c_68, c_936])).
% 7.31/2.71  tff(c_960, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_952])).
% 7.31/2.71  tff(c_2608, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2454, c_960])).
% 7.31/2.71  tff(c_2614, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2455, c_2608])).
% 7.31/2.71  tff(c_2616, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_952])).
% 7.31/2.71  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.71  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.71  tff(c_3215, plain, (![B_483, A_484, A_485]: (~v1_xboole_0(B_483) | ~r2_hidden(A_484, A_485) | ~r1_tarski(A_485, B_483))), inference(resolution, [status(thm)], [c_24, c_936])).
% 7.31/2.71  tff(c_3275, plain, (![B_497, A_498, B_499]: (~v1_xboole_0(B_497) | ~r1_tarski(A_498, B_497) | r1_tarski(A_498, B_499))), inference(resolution, [status(thm)], [c_6, c_3215])).
% 7.31/2.71  tff(c_3289, plain, (![B_500, B_501]: (~v1_xboole_0(B_500) | r1_tarski(B_500, B_501))), inference(resolution, [status(thm)], [c_14, c_3275])).
% 7.31/2.71  tff(c_120, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.71  tff(c_127, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_120])).
% 7.31/2.71  tff(c_164, plain, (![B_66, A_67]: (B_66=A_67 | ~r1_tarski(B_66, A_67) | ~r1_tarski(A_67, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.31/2.71  tff(c_178, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(resolution, [status(thm)], [c_127, c_164])).
% 7.31/2.71  tff(c_828, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(splitLeft, [status(thm)], [c_178])).
% 7.31/2.71  tff(c_3317, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_3289, c_828])).
% 7.31/2.71  tff(c_3330, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2616, c_3317])).
% 7.31/2.71  tff(c_3331, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(splitRight, [status(thm)], [c_178])).
% 7.31/2.71  tff(c_3335, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_68])).
% 7.31/2.71  tff(c_3958, plain, (![D_591, C_592, A_593, B_594]: (D_591=C_592 | ~r2_relset_1(A_593, B_594, C_592, D_591) | ~m1_subset_1(D_591, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))) | ~m1_subset_1(C_592, k1_zfmisc_1(k2_zfmisc_1(A_593, B_594))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.31/2.71  tff(c_3968, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_3958])).
% 7.31/2.71  tff(c_3987, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_3968])).
% 7.31/2.71  tff(c_4009, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_3987])).
% 7.31/2.71  tff(c_4259, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_4009])).
% 7.31/2.71  tff(c_4266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_3335, c_3331, c_4259])).
% 7.31/2.71  tff(c_4267, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3987])).
% 7.31/2.71  tff(c_4651, plain, (![C_702, A_705, B_703, E_704, D_701]: (k1_xboole_0=C_702 | v2_funct_1(D_701) | ~v2_funct_1(k1_partfun1(A_705, B_703, B_703, C_702, D_701, E_704)) | ~m1_subset_1(E_704, k1_zfmisc_1(k2_zfmisc_1(B_703, C_702))) | ~v1_funct_2(E_704, B_703, C_702) | ~v1_funct_1(E_704) | ~m1_subset_1(D_701, k1_zfmisc_1(k2_zfmisc_1(A_705, B_703))) | ~v1_funct_2(D_701, A_705, B_703) | ~v1_funct_1(D_701))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.31/2.71  tff(c_4653, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4267, c_4651])).
% 7.31/2.71  tff(c_4655, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_72, c_70, c_3335, c_3331, c_79, c_4653])).
% 7.31/2.71  tff(c_4656, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_4655])).
% 7.31/2.71  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.71  tff(c_3340, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3331, c_16])).
% 7.31/2.71  tff(c_3359, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_3340])).
% 7.31/2.71  tff(c_4688, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4656, c_3359])).
% 7.31/2.71  tff(c_4696, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4656, c_4656, c_18])).
% 7.31/2.71  tff(c_4875, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4696, c_3331])).
% 7.31/2.71  tff(c_4877, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4688, c_4875])).
% 7.31/2.71  tff(c_4879, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3340])).
% 7.31/2.71  tff(c_4878, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_3340])).
% 7.31/2.71  tff(c_4894, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_4879, c_4879, c_4878])).
% 7.31/2.71  tff(c_4895, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_4894])).
% 7.31/2.71  tff(c_4888, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4879, c_8])).
% 7.31/2.71  tff(c_4896, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4888])).
% 7.31/2.71  tff(c_4898, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4895, c_3335])).
% 7.31/2.71  tff(c_26, plain, (![C_14, B_13, A_12]: (~v1_xboole_0(C_14) | ~m1_subset_1(B_13, k1_zfmisc_1(C_14)) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.71  tff(c_5034, plain, (![A_12]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_12, '#skF_2'))), inference(resolution, [status(thm)], [c_4898, c_26])).
% 7.31/2.71  tff(c_5043, plain, (![A_731]: (~r2_hidden(A_731, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4896, c_5034])).
% 7.31/2.71  tff(c_5048, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_5043])).
% 7.31/2.71  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.31/2.71  tff(c_4886, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4879, c_4879, c_20])).
% 7.31/2.71  tff(c_4950, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4895, c_4895, c_4886])).
% 7.31/2.71  tff(c_128, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_74, c_120])).
% 7.31/2.71  tff(c_177, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_128, c_164])).
% 7.31/2.71  tff(c_3333, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_177])).
% 7.31/2.71  tff(c_4951, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4950, c_3333])).
% 7.31/2.71  tff(c_5051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5048, c_4951])).
% 7.31/2.71  tff(c_5052, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_4894])).
% 7.31/2.71  tff(c_5054, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_4888])).
% 7.31/2.71  tff(c_5056, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_5052, c_3335])).
% 7.31/2.71  tff(c_5217, plain, (![A_12]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_12, '#skF_3'))), inference(resolution, [status(thm)], [c_5056, c_26])).
% 7.31/2.71  tff(c_5226, plain, (![A_746]: (~r2_hidden(A_746, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5054, c_5217])).
% 7.31/2.71  tff(c_5231, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_5226])).
% 7.31/2.71  tff(c_4887, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4879, c_4879, c_18])).
% 7.31/2.71  tff(c_5119, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5052, c_5052, c_4887])).
% 7.31/2.71  tff(c_5120, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5119, c_3333])).
% 7.31/2.71  tff(c_5234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5231, c_5120])).
% 7.31/2.71  tff(c_5235, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_177])).
% 7.31/2.71  tff(c_5248, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_74])).
% 7.31/2.71  tff(c_5238, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_3331, c_68])).
% 7.31/2.71  tff(c_5900, plain, (![D_836, C_837, A_838, B_839]: (D_836=C_837 | ~r2_relset_1(A_838, B_839, C_837, D_836) | ~m1_subset_1(D_836, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))) | ~m1_subset_1(C_837, k1_zfmisc_1(k2_zfmisc_1(A_838, B_839))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.31/2.71  tff(c_5908, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_5900])).
% 7.31/2.71  tff(c_5923, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_5908])).
% 7.31/2.71  tff(c_6033, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5923])).
% 7.31/2.71  tff(c_6145, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_6033])).
% 7.31/2.71  tff(c_6152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_5248, c_5235, c_72, c_5238, c_3331, c_6145])).
% 7.31/2.71  tff(c_6153, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5923])).
% 7.31/2.71  tff(c_6445, plain, (![C_927, B_928, D_926, A_930, E_929]: (k1_xboole_0=C_927 | v2_funct_1(D_926) | ~v2_funct_1(k1_partfun1(A_930, B_928, B_928, C_927, D_926, E_929)) | ~m1_subset_1(E_929, k1_zfmisc_1(k2_zfmisc_1(B_928, C_927))) | ~v1_funct_2(E_929, B_928, C_927) | ~v1_funct_1(E_929) | ~m1_subset_1(D_926, k1_zfmisc_1(k2_zfmisc_1(A_930, B_928))) | ~v1_funct_2(D_926, A_930, B_928) | ~v1_funct_1(D_926))), inference(cnfTransformation, [status(thm)], [f_147])).
% 7.31/2.71  tff(c_6447, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6153, c_6445])).
% 7.31/2.71  tff(c_6449, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_5248, c_5235, c_72, c_70, c_5238, c_3331, c_79, c_6447])).
% 7.31/2.71  tff(c_6450, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_94, c_6449])).
% 7.31/2.71  tff(c_5253, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5235, c_16])).
% 7.31/2.71  tff(c_5279, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_5253])).
% 7.31/2.71  tff(c_6481, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6450, c_5279])).
% 7.31/2.71  tff(c_6657, plain, (![B_943]: (k2_zfmisc_1('#skF_2', B_943)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6450, c_6450, c_20])).
% 7.31/2.71  tff(c_6713, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6657, c_5235])).
% 7.31/2.71  tff(c_6740, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6481, c_6713])).
% 7.31/2.71  tff(c_6742, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5253])).
% 7.31/2.71  tff(c_306, plain, (![C_86, B_87, A_88]: (~v1_xboole_0(C_86) | ~m1_subset_1(B_87, k1_zfmisc_1(C_86)) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.31/2.71  tff(c_376, plain, (![B_100, A_101, A_102]: (~v1_xboole_0(B_100) | ~r2_hidden(A_101, A_102) | ~r1_tarski(A_102, B_100))), inference(resolution, [status(thm)], [c_24, c_306])).
% 7.31/2.71  tff(c_725, plain, (![B_153, A_154, B_155]: (~v1_xboole_0(B_153) | ~r1_tarski(A_154, B_153) | r1_tarski(A_154, B_155))), inference(resolution, [status(thm)], [c_6, c_376])).
% 7.31/2.71  tff(c_742, plain, (![B_156, B_157]: (~v1_xboole_0(B_156) | r1_tarski(B_156, B_157))), inference(resolution, [status(thm)], [c_14, c_725])).
% 7.31/2.71  tff(c_134, plain, (![A_62]: (m1_subset_1(k6_partfun1(A_62), k1_zfmisc_1(k2_zfmisc_1(A_62, A_62))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.31/2.71  tff(c_141, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_134])).
% 7.31/2.71  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.31/2.71  tff(c_150, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_141, c_22])).
% 7.31/2.71  tff(c_176, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_150, c_164])).
% 7.31/2.71  tff(c_183, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_176])).
% 7.31/2.71  tff(c_773, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_742, c_183])).
% 7.31/2.71  tff(c_787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_773])).
% 7.31/2.71  tff(c_788, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_176])).
% 7.31/2.71  tff(c_806, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_788, c_79])).
% 7.31/2.71  tff(c_6746, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6742, c_806])).
% 7.31/2.71  tff(c_6755, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_6746])).
% 7.31/2.71  tff(c_6756, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_64])).
% 7.31/2.71  tff(c_6827, plain, (![C_955, A_956, B_957]: (v1_relat_1(C_955) | ~m1_subset_1(C_955, k1_zfmisc_1(k2_zfmisc_1(A_956, B_957))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.31/2.71  tff(c_6848, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_6827])).
% 7.31/2.71  tff(c_7509, plain, (![C_1051, B_1052, A_1053]: (v5_relat_1(C_1051, B_1052) | ~m1_subset_1(C_1051, k1_zfmisc_1(k2_zfmisc_1(A_1053, B_1052))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.31/2.71  tff(c_7531, plain, (v5_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_68, c_7509])).
% 7.31/2.71  tff(c_7717, plain, (![A_1089, B_1090, D_1091]: (r2_relset_1(A_1089, B_1090, D_1091, D_1091) | ~m1_subset_1(D_1091, k1_zfmisc_1(k2_zfmisc_1(A_1089, B_1090))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.31/2.71  tff(c_7732, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_54, c_7717])).
% 7.31/2.71  tff(c_7786, plain, (![A_1096, B_1097, C_1098]: (k2_relset_1(A_1096, B_1097, C_1098)=k2_relat_1(C_1098) | ~m1_subset_1(C_1098, k1_zfmisc_1(k2_zfmisc_1(A_1096, B_1097))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.31/2.71  tff(c_7808, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_68, c_7786])).
% 7.31/2.71  tff(c_7819, plain, (![D_1099, C_1100, A_1101, B_1102]: (D_1099=C_1100 | ~r2_relset_1(A_1101, B_1102, C_1100, D_1099) | ~m1_subset_1(D_1099, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1102))) | ~m1_subset_1(C_1100, k1_zfmisc_1(k2_zfmisc_1(A_1101, B_1102))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.31/2.71  tff(c_7829, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_66, c_7819])).
% 7.31/2.71  tff(c_7848, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_7829])).
% 7.31/2.71  tff(c_8198, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_7848])).
% 7.31/2.71  tff(c_8299, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_48, c_8198])).
% 7.31/2.71  tff(c_8306, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_78, c_74, c_72, c_68, c_8299])).
% 7.31/2.71  tff(c_8307, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_7848])).
% 7.31/2.71  tff(c_8439, plain, (![A_1202, B_1203, C_1204, D_1205]: (k2_relset_1(A_1202, B_1203, C_1204)=B_1203 | ~r2_relset_1(B_1203, B_1203, k1_partfun1(B_1203, A_1202, A_1202, B_1203, D_1205, C_1204), k6_partfun1(B_1203)) | ~m1_subset_1(D_1205, k1_zfmisc_1(k2_zfmisc_1(B_1203, A_1202))) | ~v1_funct_2(D_1205, B_1203, A_1202) | ~v1_funct_1(D_1205) | ~m1_subset_1(C_1204, k1_zfmisc_1(k2_zfmisc_1(A_1202, B_1203))) | ~v1_funct_2(C_1204, A_1202, B_1203) | ~v1_funct_1(C_1204))), inference(cnfTransformation, [status(thm)], [f_125])).
% 7.31/2.71  tff(c_8442, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8307, c_8439])).
% 7.31/2.71  tff(c_8447, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_78, c_76, c_74, c_7732, c_7808, c_8442])).
% 7.31/2.71  tff(c_44, plain, (![B_30]: (v2_funct_2(B_30, k2_relat_1(B_30)) | ~v5_relat_1(B_30, k2_relat_1(B_30)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.31/2.71  tff(c_8459, plain, (v2_funct_2('#skF_5', k2_relat_1('#skF_5')) | ~v5_relat_1('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_8447, c_44])).
% 7.31/2.71  tff(c_8469, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6848, c_7531, c_8447, c_8459])).
% 7.31/2.71  tff(c_8471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6756, c_8469])).
% 7.31/2.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.31/2.71  
% 7.31/2.71  Inference rules
% 7.31/2.71  ----------------------
% 7.31/2.71  #Ref     : 0
% 7.31/2.71  #Sup     : 1829
% 7.31/2.71  #Fact    : 0
% 7.31/2.71  #Define  : 0
% 7.31/2.71  #Split   : 48
% 7.31/2.71  #Chain   : 0
% 7.31/2.71  #Close   : 0
% 7.31/2.71  
% 7.31/2.71  Ordering : KBO
% 7.31/2.71  
% 7.31/2.71  Simplification rules
% 7.31/2.71  ----------------------
% 7.31/2.71  #Subsume      : 191
% 7.31/2.71  #Demod        : 1342
% 7.31/2.71  #Tautology    : 759
% 7.31/2.71  #SimpNegUnit  : 12
% 7.31/2.71  #BackRed      : 198
% 7.31/2.71  
% 7.31/2.71  #Partial instantiations: 0
% 7.31/2.71  #Strategies tried      : 1
% 7.31/2.71  
% 7.31/2.71  Timing (in seconds)
% 7.31/2.71  ----------------------
% 7.31/2.72  Preprocessing        : 0.36
% 7.51/2.72  Parsing              : 0.19
% 7.51/2.72  CNF conversion       : 0.03
% 7.51/2.72  Main loop            : 1.55
% 7.51/2.72  Inferencing          : 0.56
% 7.51/2.72  Reduction            : 0.54
% 7.51/2.72  Demodulation         : 0.38
% 7.51/2.72  BG Simplification    : 0.05
% 7.51/2.72  Subsumption          : 0.25
% 7.51/2.72  Abstraction          : 0.05
% 7.51/2.72  MUC search           : 0.00
% 7.51/2.72  Cooper               : 0.00
% 7.51/2.72  Total                : 1.97
% 7.51/2.72  Index Insertion      : 0.00
% 7.51/2.72  Index Deletion       : 0.00
% 7.51/2.72  Index Matching       : 0.00
% 7.51/2.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------
