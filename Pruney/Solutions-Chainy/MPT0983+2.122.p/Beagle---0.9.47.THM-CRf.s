%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:19 EST 2020

% Result     : Theorem 6.23s
% Output     : CNFRefutation 6.49s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 318 expanded)
%              Number of leaves         :   48 ( 131 expanded)
%              Depth                    :   12
%              Number of atoms          :  237 ( 925 expanded)
%              Number of equality atoms :   45 (  98 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_170,negated_conjecture,(
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

tff(f_128,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_80,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_116,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_96,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_150,axiom,(
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

tff(f_42,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_126,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_66,plain,
    ( ~ v2_funct_2('#skF_4','#skF_1')
    | ~ v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_165,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_80,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_78,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_76,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_72,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_60,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_38,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_82,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_38])).

tff(c_1951,plain,(
    ! [F_282,D_278,B_279,C_283,A_281,E_280] :
      ( m1_subset_1(k1_partfun1(A_281,B_279,C_283,D_278,E_280,F_282),k1_zfmisc_1(k2_zfmisc_1(A_281,D_278)))
      | ~ m1_subset_1(F_282,k1_zfmisc_1(k2_zfmisc_1(C_283,D_278)))
      | ~ v1_funct_1(F_282)
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_281,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_48,plain,(
    ! [A_28] : m1_subset_1(k6_relat_1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_81,plain,(
    ! [A_28] : m1_subset_1(k6_partfun1(A_28),k1_zfmisc_1(k2_zfmisc_1(A_28,A_28))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_48])).

tff(c_68,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_1616,plain,(
    ! [D_233,C_234,A_235,B_236] :
      ( D_233 = C_234
      | ~ r2_relset_1(A_235,B_236,C_234,D_233)
      | ~ m1_subset_1(D_233,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ m1_subset_1(C_234,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1626,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_1616])).

tff(c_1645,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_1626])).

tff(c_1694,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1645])).

tff(c_1957,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1951,c_1694])).

tff(c_1989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_1957])).

tff(c_1990,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_1645])).

tff(c_2906,plain,(
    ! [C_382,B_383,A_385,D_381,E_384] :
      ( k1_xboole_0 = C_382
      | v2_funct_1(D_381)
      | ~ v2_funct_1(k1_partfun1(A_385,B_383,B_383,C_382,D_381,E_384))
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(B_383,C_382)))
      | ~ v1_funct_2(E_384,B_383,C_382)
      | ~ v1_funct_1(E_384)
      | ~ m1_subset_1(D_381,k1_zfmisc_1(k2_zfmisc_1(A_385,B_383)))
      | ~ v1_funct_2(D_381,A_385,B_383)
      | ~ v1_funct_1(D_381) ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_2908,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1990,c_2906])).

tff(c_2910,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_76,c_74,c_72,c_70,c_82,c_2908])).

tff(c_2911,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_2910])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_2947,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2911,c_2])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2945,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2911,c_2911,c_16])).

tff(c_205,plain,(
    ! [B_63,A_64] :
      ( v1_xboole_0(B_63)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_64))
      | ~ v1_xboole_0(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_205])).

tff(c_225,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_223])).

tff(c_3212,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2945,c_225])).

tff(c_3216,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2947,c_3212])).

tff(c_3217,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_223])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_3247,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_3217,c_4])).

tff(c_106,plain,(
    ! [A_57] : k6_relat_1(A_57) = k6_partfun1(A_57) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_34,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_112,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_34])).

tff(c_125,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_82])).

tff(c_3257,plain,(
    v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3247,c_125])).

tff(c_3264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_165,c_3257])).

tff(c_3265,plain,(
    ~ v2_funct_2('#skF_4','#skF_1') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_26,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3338,plain,(
    ! [B_408,A_409] :
      ( v1_relat_1(B_408)
      | ~ m1_subset_1(B_408,k1_zfmisc_1(A_409))
      | ~ v1_relat_1(A_409) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_3347,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_70,c_3338])).

tff(c_3359,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3347])).

tff(c_3383,plain,(
    ! [C_413,B_414,A_415] :
      ( v5_relat_1(C_413,B_414)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_415,B_414))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3400,plain,(
    v5_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_3383])).

tff(c_3350,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_76,c_3338])).

tff(c_3362,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3350])).

tff(c_32,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_84,plain,(
    ! [A_19] : k2_relat_1(k6_partfun1(A_19)) = A_19 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_32])).

tff(c_4032,plain,(
    ! [D_497,E_499,C_502,F_501,A_500,B_498] :
      ( m1_subset_1(k1_partfun1(A_500,B_498,C_502,D_497,E_499,F_501),k1_zfmisc_1(k2_zfmisc_1(A_500,D_497)))
      | ~ m1_subset_1(F_501,k1_zfmisc_1(k2_zfmisc_1(C_502,D_497)))
      | ~ v1_funct_1(F_501)
      | ~ m1_subset_1(E_499,k1_zfmisc_1(k2_zfmisc_1(A_500,B_498)))
      | ~ v1_funct_1(E_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3697,plain,(
    ! [D_453,C_454,A_455,B_456] :
      ( D_453 = C_454
      | ~ r2_relset_1(A_455,B_456,C_454,D_453)
      | ~ m1_subset_1(D_453,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456)))
      | ~ m1_subset_1(C_454,k1_zfmisc_1(k2_zfmisc_1(A_455,B_456))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3707,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_68,c_3697])).

tff(c_3726,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_3707])).

tff(c_3778,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_3726])).

tff(c_4035,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4032,c_3778])).

tff(c_4069,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_74,c_70,c_4035])).

tff(c_4070,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_3726])).

tff(c_4261,plain,(
    ! [B_530,D_532,E_533,C_534,A_529,F_531] :
      ( k1_partfun1(A_529,B_530,C_534,D_532,E_533,F_531) = k5_relat_1(E_533,F_531)
      | ~ m1_subset_1(F_531,k1_zfmisc_1(k2_zfmisc_1(C_534,D_532)))
      | ~ v1_funct_1(F_531)
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ v1_funct_1(E_533) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4265,plain,(
    ! [A_529,B_530,E_533] :
      ( k1_partfun1(A_529,B_530,'#skF_2','#skF_1',E_533,'#skF_4') = k5_relat_1(E_533,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_533,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530)))
      | ~ v1_funct_1(E_533) ) ),
    inference(resolution,[status(thm)],[c_70,c_4261])).

tff(c_4427,plain,(
    ! [A_556,B_557,E_558] :
      ( k1_partfun1(A_556,B_557,'#skF_2','#skF_1',E_558,'#skF_4') = k5_relat_1(E_558,'#skF_4')
      | ~ m1_subset_1(E_558,k1_zfmisc_1(k2_zfmisc_1(A_556,B_557)))
      | ~ v1_funct_1(E_558) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_4265])).

tff(c_4439,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_76,c_4427])).

tff(c_4453,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4070,c_4439])).

tff(c_28,plain,(
    ! [A_16,B_18] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_16,B_18)),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_4460,plain,
    ( r1_tarski(k2_relat_1(k6_partfun1('#skF_1')),k2_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4453,c_28])).

tff(c_4466,plain,(
    r1_tarski('#skF_1',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3362,c_3359,c_84,c_4460])).

tff(c_3467,plain,(
    ! [B_428,A_429] :
      ( r1_tarski(k2_relat_1(B_428),A_429)
      | ~ v5_relat_1(B_428,A_429)
      | ~ v1_relat_1(B_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6,plain,(
    ! [B_3,A_2] :
      ( B_3 = A_2
      | ~ r1_tarski(B_3,A_2)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3480,plain,(
    ! [B_428,A_429] :
      ( k2_relat_1(B_428) = A_429
      | ~ r1_tarski(A_429,k2_relat_1(B_428))
      | ~ v5_relat_1(B_428,A_429)
      | ~ v1_relat_1(B_428) ) ),
    inference(resolution,[status(thm)],[c_3467,c_6])).

tff(c_4470,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v5_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4466,c_3480])).

tff(c_4475,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3359,c_3400,c_4470])).

tff(c_10,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_3435,plain,(
    ! [B_422,A_423] :
      ( v5_relat_1(B_422,A_423)
      | ~ r1_tarski(k2_relat_1(B_422),A_423)
      | ~ v1_relat_1(B_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_3450,plain,(
    ! [B_422] :
      ( v5_relat_1(B_422,k2_relat_1(B_422))
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_10,c_3435])).

tff(c_3535,plain,(
    ! [B_437] :
      ( v2_funct_2(B_437,k2_relat_1(B_437))
      | ~ v5_relat_1(B_437,k2_relat_1(B_437))
      | ~ v1_relat_1(B_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_3559,plain,(
    ! [B_422] :
      ( v2_funct_2(B_422,k2_relat_1(B_422))
      | ~ v1_relat_1(B_422) ) ),
    inference(resolution,[status(thm)],[c_3450,c_3535])).

tff(c_4488,plain,
    ( v2_funct_2('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4475,c_3559])).

tff(c_4508,plain,(
    v2_funct_2('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3359,c_4488])).

tff(c_4510,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3265,c_4508])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:40:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.23/2.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.23  
% 6.23/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.23/2.23  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v2_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.23/2.23  
% 6.23/2.23  %Foreground sorts:
% 6.23/2.23  
% 6.23/2.23  
% 6.23/2.23  %Background operators:
% 6.23/2.23  
% 6.23/2.23  
% 6.23/2.23  %Foreground operators:
% 6.23/2.23  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.23/2.23  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.23/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.23/2.23  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 6.23/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.23/2.23  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.23/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.23/2.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.23/2.23  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.23/2.23  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.23/2.23  tff('#skF_2', type, '#skF_2': $i).
% 6.23/2.23  tff('#skF_3', type, '#skF_3': $i).
% 6.23/2.23  tff('#skF_1', type, '#skF_1': $i).
% 6.23/2.23  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 6.23/2.23  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.23/2.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.23/2.23  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 6.23/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.23/2.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.23/2.23  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.23/2.23  tff('#skF_4', type, '#skF_4': $i).
% 6.23/2.23  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 6.23/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.23/2.23  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.23/2.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.23/2.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.23/2.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.23/2.23  
% 6.49/2.27  tff(f_170, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 6.49/2.27  tff(f_128, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 6.49/2.27  tff(f_80, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 6.49/2.27  tff(f_116, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 6.49/2.27  tff(f_96, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 6.49/2.27  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 6.49/2.27  tff(f_150, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 6.49/2.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.49/2.27  tff(f_42, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.49/2.27  tff(f_49, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 6.49/2.27  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 6.49/2.27  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 6.49/2.27  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.49/2.27  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.49/2.27  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.49/2.27  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 6.49/2.27  tff(f_126, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 6.49/2.27  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 6.49/2.27  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.49/2.27  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.49/2.27  tff(f_104, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 6.49/2.27  tff(c_66, plain, (~v2_funct_2('#skF_4', '#skF_1') | ~v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_165, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_66])).
% 6.49/2.27  tff(c_80, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_78, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_76, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_72, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_60, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.49/2.27  tff(c_38, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.49/2.27  tff(c_82, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_38])).
% 6.49/2.27  tff(c_1951, plain, (![F_282, D_278, B_279, C_283, A_281, E_280]: (m1_subset_1(k1_partfun1(A_281, B_279, C_283, D_278, E_280, F_282), k1_zfmisc_1(k2_zfmisc_1(A_281, D_278))) | ~m1_subset_1(F_282, k1_zfmisc_1(k2_zfmisc_1(C_283, D_278))) | ~v1_funct_1(F_282) | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_281, B_279))) | ~v1_funct_1(E_280))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.49/2.27  tff(c_48, plain, (![A_28]: (m1_subset_1(k6_relat_1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.49/2.27  tff(c_81, plain, (![A_28]: (m1_subset_1(k6_partfun1(A_28), k1_zfmisc_1(k2_zfmisc_1(A_28, A_28))))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_48])).
% 6.49/2.27  tff(c_68, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_170])).
% 6.49/2.27  tff(c_1616, plain, (![D_233, C_234, A_235, B_236]: (D_233=C_234 | ~r2_relset_1(A_235, B_236, C_234, D_233) | ~m1_subset_1(D_233, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~m1_subset_1(C_234, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.49/2.27  tff(c_1626, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_1616])).
% 6.49/2.27  tff(c_1645, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_1626])).
% 6.49/2.27  tff(c_1694, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1645])).
% 6.49/2.27  tff(c_1957, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1951, c_1694])).
% 6.49/2.27  tff(c_1989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_1957])).
% 6.49/2.27  tff(c_1990, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_1645])).
% 6.49/2.27  tff(c_2906, plain, (![C_382, B_383, A_385, D_381, E_384]: (k1_xboole_0=C_382 | v2_funct_1(D_381) | ~v2_funct_1(k1_partfun1(A_385, B_383, B_383, C_382, D_381, E_384)) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(B_383, C_382))) | ~v1_funct_2(E_384, B_383, C_382) | ~v1_funct_1(E_384) | ~m1_subset_1(D_381, k1_zfmisc_1(k2_zfmisc_1(A_385, B_383))) | ~v1_funct_2(D_381, A_385, B_383) | ~v1_funct_1(D_381))), inference(cnfTransformation, [status(thm)], [f_150])).
% 6.49/2.27  tff(c_2908, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1990, c_2906])).
% 6.49/2.27  tff(c_2910, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_76, c_74, c_72, c_70, c_82, c_2908])).
% 6.49/2.27  tff(c_2911, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_165, c_2910])).
% 6.49/2.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.49/2.27  tff(c_2947, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2911, c_2])).
% 6.49/2.27  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.49/2.27  tff(c_2945, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2911, c_2911, c_16])).
% 6.49/2.27  tff(c_205, plain, (![B_63, A_64]: (v1_xboole_0(B_63) | ~m1_subset_1(B_63, k1_zfmisc_1(A_64)) | ~v1_xboole_0(A_64))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.49/2.27  tff(c_223, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_205])).
% 6.49/2.27  tff(c_225, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_223])).
% 6.49/2.27  tff(c_3212, plain, (~v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2945, c_225])).
% 6.49/2.27  tff(c_3216, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2947, c_3212])).
% 6.49/2.27  tff(c_3217, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_223])).
% 6.49/2.27  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.49/2.27  tff(c_3247, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_3217, c_4])).
% 6.49/2.27  tff(c_106, plain, (![A_57]: (k6_relat_1(A_57)=k6_partfun1(A_57))), inference(cnfTransformation, [status(thm)], [f_128])).
% 6.49/2.27  tff(c_34, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 6.49/2.27  tff(c_112, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_106, c_34])).
% 6.49/2.27  tff(c_125, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_112, c_82])).
% 6.49/2.27  tff(c_3257, plain, (v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3247, c_125])).
% 6.49/2.27  tff(c_3264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_165, c_3257])).
% 6.49/2.27  tff(c_3265, plain, (~v2_funct_2('#skF_4', '#skF_1')), inference(splitRight, [status(thm)], [c_66])).
% 6.49/2.27  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 6.49/2.27  tff(c_3338, plain, (![B_408, A_409]: (v1_relat_1(B_408) | ~m1_subset_1(B_408, k1_zfmisc_1(A_409)) | ~v1_relat_1(A_409))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.49/2.27  tff(c_3347, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_70, c_3338])).
% 6.49/2.27  tff(c_3359, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3347])).
% 6.49/2.27  tff(c_3383, plain, (![C_413, B_414, A_415]: (v5_relat_1(C_413, B_414) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_415, B_414))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.49/2.27  tff(c_3400, plain, (v5_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_3383])).
% 6.49/2.27  tff(c_3350, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_76, c_3338])).
% 6.49/2.27  tff(c_3362, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_3350])).
% 6.49/2.27  tff(c_32, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.49/2.27  tff(c_84, plain, (![A_19]: (k2_relat_1(k6_partfun1(A_19))=A_19)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_32])).
% 6.49/2.27  tff(c_4032, plain, (![D_497, E_499, C_502, F_501, A_500, B_498]: (m1_subset_1(k1_partfun1(A_500, B_498, C_502, D_497, E_499, F_501), k1_zfmisc_1(k2_zfmisc_1(A_500, D_497))) | ~m1_subset_1(F_501, k1_zfmisc_1(k2_zfmisc_1(C_502, D_497))) | ~v1_funct_1(F_501) | ~m1_subset_1(E_499, k1_zfmisc_1(k2_zfmisc_1(A_500, B_498))) | ~v1_funct_1(E_499))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.49/2.27  tff(c_3697, plain, (![D_453, C_454, A_455, B_456]: (D_453=C_454 | ~r2_relset_1(A_455, B_456, C_454, D_453) | ~m1_subset_1(D_453, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))) | ~m1_subset_1(C_454, k1_zfmisc_1(k2_zfmisc_1(A_455, B_456))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 6.49/2.27  tff(c_3707, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_68, c_3697])).
% 6.49/2.27  tff(c_3726, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_3707])).
% 6.49/2.27  tff(c_3778, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_3726])).
% 6.49/2.27  tff(c_4035, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_4032, c_3778])).
% 6.49/2.27  tff(c_4069, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_74, c_70, c_4035])).
% 6.49/2.27  tff(c_4070, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_3726])).
% 6.49/2.27  tff(c_4261, plain, (![B_530, D_532, E_533, C_534, A_529, F_531]: (k1_partfun1(A_529, B_530, C_534, D_532, E_533, F_531)=k5_relat_1(E_533, F_531) | ~m1_subset_1(F_531, k1_zfmisc_1(k2_zfmisc_1(C_534, D_532))) | ~v1_funct_1(F_531) | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~v1_funct_1(E_533))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.49/2.27  tff(c_4265, plain, (![A_529, B_530, E_533]: (k1_partfun1(A_529, B_530, '#skF_2', '#skF_1', E_533, '#skF_4')=k5_relat_1(E_533, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_533, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))) | ~v1_funct_1(E_533))), inference(resolution, [status(thm)], [c_70, c_4261])).
% 6.49/2.27  tff(c_4427, plain, (![A_556, B_557, E_558]: (k1_partfun1(A_556, B_557, '#skF_2', '#skF_1', E_558, '#skF_4')=k5_relat_1(E_558, '#skF_4') | ~m1_subset_1(E_558, k1_zfmisc_1(k2_zfmisc_1(A_556, B_557))) | ~v1_funct_1(E_558))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_4265])).
% 6.49/2.27  tff(c_4439, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_76, c_4427])).
% 6.49/2.27  tff(c_4453, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4070, c_4439])).
% 6.49/2.27  tff(c_28, plain, (![A_16, B_18]: (r1_tarski(k2_relat_1(k5_relat_1(A_16, B_18)), k2_relat_1(B_18)) | ~v1_relat_1(B_18) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.49/2.27  tff(c_4460, plain, (r1_tarski(k2_relat_1(k6_partfun1('#skF_1')), k2_relat_1('#skF_4')) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4453, c_28])).
% 6.49/2.27  tff(c_4466, plain, (r1_tarski('#skF_1', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3362, c_3359, c_84, c_4460])).
% 6.49/2.27  tff(c_3467, plain, (![B_428, A_429]: (r1_tarski(k2_relat_1(B_428), A_429) | ~v5_relat_1(B_428, A_429) | ~v1_relat_1(B_428))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.49/2.27  tff(c_6, plain, (![B_3, A_2]: (B_3=A_2 | ~r1_tarski(B_3, A_2) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.49/2.27  tff(c_3480, plain, (![B_428, A_429]: (k2_relat_1(B_428)=A_429 | ~r1_tarski(A_429, k2_relat_1(B_428)) | ~v5_relat_1(B_428, A_429) | ~v1_relat_1(B_428))), inference(resolution, [status(thm)], [c_3467, c_6])).
% 6.49/2.27  tff(c_4470, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v5_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4466, c_3480])).
% 6.49/2.27  tff(c_4475, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3359, c_3400, c_4470])).
% 6.49/2.27  tff(c_10, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 6.49/2.27  tff(c_3435, plain, (![B_422, A_423]: (v5_relat_1(B_422, A_423) | ~r1_tarski(k2_relat_1(B_422), A_423) | ~v1_relat_1(B_422))), inference(cnfTransformation, [status(thm)], [f_62])).
% 6.49/2.27  tff(c_3450, plain, (![B_422]: (v5_relat_1(B_422, k2_relat_1(B_422)) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_10, c_3435])).
% 6.49/2.27  tff(c_3535, plain, (![B_437]: (v2_funct_2(B_437, k2_relat_1(B_437)) | ~v5_relat_1(B_437, k2_relat_1(B_437)) | ~v1_relat_1(B_437))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.49/2.27  tff(c_3559, plain, (![B_422]: (v2_funct_2(B_422, k2_relat_1(B_422)) | ~v1_relat_1(B_422))), inference(resolution, [status(thm)], [c_3450, c_3535])).
% 6.49/2.27  tff(c_4488, plain, (v2_funct_2('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4475, c_3559])).
% 6.49/2.27  tff(c_4508, plain, (v2_funct_2('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3359, c_4488])).
% 6.49/2.27  tff(c_4510, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3265, c_4508])).
% 6.49/2.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.49/2.27  
% 6.49/2.27  Inference rules
% 6.49/2.27  ----------------------
% 6.49/2.27  #Ref     : 0
% 6.49/2.27  #Sup     : 924
% 6.49/2.27  #Fact    : 0
% 6.49/2.27  #Define  : 0
% 6.49/2.27  #Split   : 17
% 6.49/2.27  #Chain   : 0
% 6.49/2.27  #Close   : 0
% 6.49/2.27  
% 6.49/2.27  Ordering : KBO
% 6.49/2.27  
% 6.49/2.27  Simplification rules
% 6.49/2.27  ----------------------
% 6.49/2.27  #Subsume      : 130
% 6.49/2.27  #Demod        : 968
% 6.49/2.27  #Tautology    : 289
% 6.49/2.27  #SimpNegUnit  : 6
% 6.49/2.27  #BackRed      : 107
% 6.49/2.27  
% 6.49/2.27  #Partial instantiations: 0
% 6.49/2.27  #Strategies tried      : 1
% 6.49/2.27  
% 6.49/2.27  Timing (in seconds)
% 6.49/2.27  ----------------------
% 6.67/2.28  Preprocessing        : 0.34
% 6.67/2.28  Parsing              : 0.17
% 6.67/2.28  CNF conversion       : 0.02
% 6.67/2.28  Main loop            : 1.08
% 6.67/2.28  Inferencing          : 0.38
% 6.67/2.28  Reduction            : 0.39
% 6.67/2.28  Demodulation         : 0.29
% 6.67/2.28  BG Simplification    : 0.04
% 6.67/2.28  Subsumption          : 0.18
% 6.67/2.28  Abstraction          : 0.05
% 6.67/2.28  MUC search           : 0.00
% 6.67/2.28  Cooper               : 0.00
% 6.67/2.28  Total                : 1.50
% 6.67/2.28  Index Insertion      : 0.00
% 6.67/2.28  Index Deletion       : 0.00
% 6.67/2.28  Index Matching       : 0.00
% 6.67/2.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
