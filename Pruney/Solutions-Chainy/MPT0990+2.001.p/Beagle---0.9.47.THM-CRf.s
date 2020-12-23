%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 9.15s
% Output     : CNFRefutation 9.15s
% Verified   : 
% Statistics : Number of formulae       :  179 (1021 expanded)
%              Number of leaves         :   46 ( 379 expanded)
%              Depth                    :   18
%              Number of atoms          :  445 (4381 expanded)
%              Number of equality atoms :  143 (1351 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_235,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_193,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_134,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_132,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_122,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_106,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_118,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_177,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_88,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k1_relat_1(A),k2_relat_1(B))
           => k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & k2_relat_1(B) = k1_relat_1(A)
              & k5_relat_1(B,A) = k6_relat_1(k2_relat_1(A)) )
           => B = k2_funct_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

tff(f_67,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_209,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_70,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_86,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_84,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_82,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_278,plain,(
    ! [A_100,B_101,C_102] :
      ( k2_relset_1(A_100,B_101,C_102) = k2_relat_1(C_102)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_290,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_278])).

tff(c_2808,plain,(
    ! [C_294,A_295,B_296] :
      ( v1_funct_1(k2_funct_1(C_294))
      | k2_relset_1(A_295,B_296,C_294) != B_296
      | ~ v2_funct_1(C_294)
      | ~ m1_subset_1(C_294,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_2(C_294,A_295,B_296)
      | ~ v1_funct_1(C_294) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_2814,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_2808])).

tff(c_2823,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_290,c_2814])).

tff(c_2827,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2823])).

tff(c_92,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_90,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_88,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_48,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_18,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_94,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_80,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_2330,plain,(
    ! [B_261,A_260,E_264,F_262,C_265,D_263] :
      ( k1_partfun1(A_260,B_261,C_265,D_263,E_264,F_262) = k5_relat_1(E_264,F_262)
      | ~ m1_subset_1(F_262,k1_zfmisc_1(k2_zfmisc_1(C_265,D_263)))
      | ~ v1_funct_1(F_262)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ v1_funct_1(E_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_2336,plain,(
    ! [A_260,B_261,E_264] :
      ( k1_partfun1(A_260,B_261,'#skF_2','#skF_1',E_264,'#skF_4') = k5_relat_1(E_264,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261)))
      | ~ v1_funct_1(E_264) ) ),
    inference(resolution,[status(thm)],[c_82,c_2330])).

tff(c_2350,plain,(
    ! [A_270,B_271,E_272] :
      ( k1_partfun1(A_270,B_271,'#skF_2','#skF_1',E_272,'#skF_4') = k5_relat_1(E_272,'#skF_4')
      | ~ m1_subset_1(E_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_1(E_272) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_2336])).

tff(c_2362,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_2350])).

tff(c_2370,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2362])).

tff(c_44,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_78,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_486,plain,(
    ! [D_115,C_116,A_117,B_118] :
      ( D_115 = C_116
      | ~ r2_relset_1(A_117,B_118,C_116,D_115)
      | ~ m1_subset_1(D_115,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118))) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_494,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_78,c_486])).

tff(c_509,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_494])).

tff(c_696,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_509])).

tff(c_2377,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2370,c_696])).

tff(c_2605,plain,(
    ! [A_288,E_289,B_286,C_285,D_290,F_287] :
      ( m1_subset_1(k1_partfun1(A_288,B_286,C_285,D_290,E_289,F_287),k1_zfmisc_1(k2_zfmisc_1(A_288,D_290)))
      | ~ m1_subset_1(F_287,k1_zfmisc_1(k2_zfmisc_1(C_285,D_290)))
      | ~ v1_funct_1(F_287)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_288,B_286)))
      | ~ v1_funct_1(E_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2662,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2370,c_2605])).

tff(c_2691,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_88,c_86,c_82,c_2662])).

tff(c_2693,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2377,c_2691])).

tff(c_2694,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_509])).

tff(c_4581,plain,(
    ! [D_393,E_389,A_392,C_390,B_391] :
      ( k1_xboole_0 = C_390
      | v2_funct_1(E_389)
      | k2_relset_1(A_392,B_391,D_393) != B_391
      | ~ v2_funct_1(k1_partfun1(A_392,B_391,B_391,C_390,D_393,E_389))
      | ~ m1_subset_1(E_389,k1_zfmisc_1(k2_zfmisc_1(B_391,C_390)))
      | ~ v1_funct_2(E_389,B_391,C_390)
      | ~ v1_funct_1(E_389)
      | ~ m1_subset_1(D_393,k1_zfmisc_1(k2_zfmisc_1(A_392,B_391)))
      | ~ v1_funct_2(D_393,A_392,B_391)
      | ~ v1_funct_1(D_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_4587,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2694,c_4581])).

tff(c_4595,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_90,c_88,c_86,c_84,c_82,c_94,c_80,c_4587])).

tff(c_4597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2827,c_74,c_4595])).

tff(c_4598,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_4600,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4598])).

tff(c_134,plain,(
    ! [C_71,A_72,B_73] :
      ( v1_relat_1(C_71)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_134])).

tff(c_203,plain,(
    ! [C_88,A_89,B_90] :
      ( v4_relat_1(C_88,A_89)
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_89,B_90))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_214,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_82,c_203])).

tff(c_14,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_96,plain,(
    ! [A_11] : k2_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_5169,plain,(
    ! [C_439,B_435,A_434,D_437,F_436,E_438] :
      ( k1_partfun1(A_434,B_435,C_439,D_437,E_438,F_436) = k5_relat_1(E_438,F_436)
      | ~ m1_subset_1(F_436,k1_zfmisc_1(k2_zfmisc_1(C_439,D_437)))
      | ~ v1_funct_1(F_436)
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435)))
      | ~ v1_funct_1(E_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_5173,plain,(
    ! [A_434,B_435,E_438] :
      ( k1_partfun1(A_434,B_435,'#skF_2','#skF_1',E_438,'#skF_4') = k5_relat_1(E_438,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_438,k1_zfmisc_1(k2_zfmisc_1(A_434,B_435)))
      | ~ v1_funct_1(E_438) ) ),
    inference(resolution,[status(thm)],[c_82,c_5169])).

tff(c_5183,plain,(
    ! [A_440,B_441,E_442] :
      ( k1_partfun1(A_440,B_441,'#skF_2','#skF_1',E_442,'#skF_4') = k5_relat_1(E_442,'#skF_4')
      | ~ m1_subset_1(E_442,k1_zfmisc_1(k2_zfmisc_1(A_440,B_441)))
      | ~ v1_funct_1(E_442) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5173])).

tff(c_5192,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_5183])).

tff(c_5199,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2694,c_5192])).

tff(c_6,plain,(
    ! [B_5,A_4] :
      ( r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v4_relat_1(B_5,A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_147,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_134])).

tff(c_287,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_278])).

tff(c_292,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_287])).

tff(c_10,plain,(
    ! [B_10,A_8] :
      ( k2_relat_1(k5_relat_1(B_10,A_8)) = k2_relat_1(A_8)
      | ~ r1_tarski(k1_relat_1(A_8),k2_relat_1(B_10))
      | ~ v1_relat_1(B_10)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_318,plain,(
    ! [A_8] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_8)) = k2_relat_1(A_8)
      | ~ r1_tarski(k1_relat_1(A_8),'#skF_2')
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_10])).

tff(c_337,plain,(
    ! [A_106] :
      ( k2_relat_1(k5_relat_1('#skF_3',A_106)) = k2_relat_1(A_106)
      | ~ r1_tarski(k1_relat_1(A_106),'#skF_2')
      | ~ v1_relat_1(A_106) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_318])).

tff(c_348,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_5)) = k2_relat_1(B_5)
      | ~ v4_relat_1(B_5,'#skF_2')
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_337])).

tff(c_5206,plain,
    ( k2_relat_1(k6_partfun1('#skF_1')) = k2_relat_1('#skF_4')
    | ~ v4_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5199,c_348])).

tff(c_5212,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_214,c_96,c_5206])).

tff(c_5214,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4600,c_5212])).

tff(c_5216,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4598])).

tff(c_4599,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2823])).

tff(c_24,plain,(
    ! [A_14,B_16] :
      ( k2_funct_1(A_14) = B_16
      | k6_relat_1(k2_relat_1(A_14)) != k5_relat_1(B_16,A_14)
      | k2_relat_1(B_16) != k1_relat_1(A_14)
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7367,plain,(
    ! [A_555,B_556] :
      ( k2_funct_1(A_555) = B_556
      | k6_partfun1(k2_relat_1(A_555)) != k5_relat_1(B_556,A_555)
      | k2_relat_1(B_556) != k1_relat_1(A_555)
      | ~ v2_funct_1(A_555)
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ v1_funct_1(A_555)
      | ~ v1_relat_1(A_555) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_24])).

tff(c_7375,plain,(
    ! [B_556] :
      ( k2_funct_1('#skF_4') = B_556
      | k5_relat_1(B_556,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_556) != k1_relat_1('#skF_4')
      | ~ v2_funct_1('#skF_4')
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5216,c_7367])).

tff(c_7404,plain,(
    ! [B_557] :
      ( k2_funct_1('#skF_4') = B_557
      | k5_relat_1(B_557,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_557) != k1_relat_1('#skF_4')
      | ~ v1_funct_1(B_557)
      | ~ v1_relat_1(B_557) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_4599,c_7375])).

tff(c_7410,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_147,c_7404])).

tff(c_7426,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k1_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_292,c_7410])).

tff(c_7433,plain,(
    k1_relat_1('#skF_4') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7426])).

tff(c_22,plain,(
    ! [A_13] :
      ( k1_relat_1(k2_funct_1(A_13)) = k2_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_231,plain,(
    ! [A_92] : v4_relat_1(k6_partfun1(A_92),A_92) ),
    inference(resolution,[status(thm)],[c_44,c_203])).

tff(c_16,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_95,plain,(
    ! [A_12] : v1_relat_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_12,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_97,plain,(
    ! [A_11] : k1_relat_1(k6_partfun1(A_11)) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_167,plain,(
    ! [B_76,A_77] :
      ( r1_tarski(k1_relat_1(B_76),A_77)
      | ~ v4_relat_1(B_76,A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_170,plain,(
    ! [A_11,A_77] :
      ( r1_tarski(A_11,A_77)
      | ~ v4_relat_1(k6_partfun1(A_11),A_77)
      | ~ v1_relat_1(k6_partfun1(A_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_167])).

tff(c_172,plain,(
    ! [A_11,A_77] :
      ( r1_tarski(A_11,A_77)
      | ~ v4_relat_1(k6_partfun1(A_11),A_77) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_170])).

tff(c_236,plain,(
    ! [A_93] : r1_tarski(A_93,A_93) ),
    inference(resolution,[status(thm)],[c_231,c_172])).

tff(c_4,plain,(
    ! [B_5,A_4] :
      ( v4_relat_1(B_5,A_4)
      | ~ r1_tarski(k1_relat_1(B_5),A_4)
      | ~ v1_relat_1(B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_242,plain,(
    ! [B_94] :
      ( v4_relat_1(B_94,k1_relat_1(B_94))
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_236,c_4])).

tff(c_249,plain,(
    ! [A_13] :
      ( v4_relat_1(k2_funct_1(A_13),k2_relat_1(A_13))
      | ~ v1_relat_1(k2_funct_1(A_13))
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_242])).

tff(c_5221,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5216,c_249])).

tff(c_5234,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_4599,c_5221])).

tff(c_5275,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5234])).

tff(c_5217,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5216,c_290])).

tff(c_5641,plain,(
    ! [C_481,B_482,A_483] :
      ( m1_subset_1(k2_funct_1(C_481),k1_zfmisc_1(k2_zfmisc_1(B_482,A_483)))
      | k2_relset_1(A_483,B_482,C_481) != B_482
      | ~ v2_funct_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_483,B_482)))
      | ~ v1_funct_2(C_481,A_483,B_482)
      | ~ v1_funct_1(C_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_193])).

tff(c_26,plain,(
    ! [C_19,A_17,B_18] :
      ( v1_relat_1(C_19)
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_7152,plain,(
    ! [C_547,A_548,B_549] :
      ( v1_relat_1(k2_funct_1(C_547))
      | k2_relset_1(A_548,B_549,C_547) != B_549
      | ~ v2_funct_1(C_547)
      | ~ m1_subset_1(C_547,k1_zfmisc_1(k2_zfmisc_1(A_548,B_549)))
      | ~ v1_funct_2(C_547,A_548,B_549)
      | ~ v1_funct_1(C_547) ) ),
    inference(resolution,[status(thm)],[c_5641,c_26])).

tff(c_7185,plain,
    ( v1_relat_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_7152])).

tff(c_7217,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_4599,c_5217,c_7185])).

tff(c_7219,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5275,c_7217])).

tff(c_7221,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5234])).

tff(c_7220,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_5234])).

tff(c_7993,plain,(
    ! [A_610,C_611,B_612] :
      ( k6_partfun1(A_610) = k5_relat_1(C_611,k2_funct_1(C_611))
      | k1_xboole_0 = B_612
      | ~ v2_funct_1(C_611)
      | k2_relset_1(A_610,B_612,C_611) != B_612
      | ~ m1_subset_1(C_611,k1_zfmisc_1(k2_zfmisc_1(A_610,B_612)))
      | ~ v1_funct_2(C_611,A_610,B_612)
      | ~ v1_funct_1(C_611) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_7999,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_7993])).

tff(c_8008,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_5217,c_4599,c_7999])).

tff(c_8009,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8008])).

tff(c_293,plain,(
    ! [B_103,A_104] :
      ( k2_relat_1(k5_relat_1(B_103,A_104)) = k2_relat_1(A_104)
      | ~ r1_tarski(k1_relat_1(A_104),k2_relat_1(B_103))
      | ~ v1_relat_1(B_103)
      | ~ v1_relat_1(A_104) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_310,plain,(
    ! [B_103,B_5] :
      ( k2_relat_1(k5_relat_1(B_103,B_5)) = k2_relat_1(B_5)
      | ~ v1_relat_1(B_103)
      | ~ v4_relat_1(B_5,k2_relat_1(B_103))
      | ~ v1_relat_1(B_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_293])).

tff(c_5227,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_5)) = k2_relat_1(B_5)
      | ~ v1_relat_1('#skF_4')
      | ~ v4_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5216,c_310])).

tff(c_5238,plain,(
    ! [B_5] :
      ( k2_relat_1(k5_relat_1('#skF_4',B_5)) = k2_relat_1(B_5)
      | ~ v4_relat_1(B_5,'#skF_1')
      | ~ v1_relat_1(B_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_5227])).

tff(c_8020,plain,
    ( k2_relat_1(k6_partfun1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_4'))
    | ~ v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8009,c_5238])).

tff(c_8026,plain,(
    k2_relat_1(k2_funct_1('#skF_4')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7221,c_7220,c_96,c_8020])).

tff(c_20,plain,(
    ! [A_13] :
      ( k2_relat_1(k2_funct_1(A_13)) = k1_relat_1(A_13)
      | ~ v2_funct_1(A_13)
      | ~ v1_funct_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8049,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8026,c_20])).

tff(c_8068,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_4599,c_8049])).

tff(c_8070,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7433,c_8068])).

tff(c_8071,plain,
    ( k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7426])).

tff(c_8164,plain,(
    k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_8071])).

tff(c_8354,plain,(
    ! [D_634,C_636,F_633,E_635,A_631,B_632] :
      ( k1_partfun1(A_631,B_632,C_636,D_634,E_635,F_633) = k5_relat_1(E_635,F_633)
      | ~ m1_subset_1(F_633,k1_zfmisc_1(k2_zfmisc_1(C_636,D_634)))
      | ~ v1_funct_1(F_633)
      | ~ m1_subset_1(E_635,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632)))
      | ~ v1_funct_1(E_635) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_8358,plain,(
    ! [A_631,B_632,E_635] :
      ( k1_partfun1(A_631,B_632,'#skF_2','#skF_1',E_635,'#skF_4') = k5_relat_1(E_635,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_635,k1_zfmisc_1(k2_zfmisc_1(A_631,B_632)))
      | ~ v1_funct_1(E_635) ) ),
    inference(resolution,[status(thm)],[c_82,c_8354])).

tff(c_8483,plain,(
    ! [A_648,B_649,E_650] :
      ( k1_partfun1(A_648,B_649,'#skF_2','#skF_1',E_650,'#skF_4') = k5_relat_1(E_650,'#skF_4')
      | ~ m1_subset_1(E_650,k1_zfmisc_1(k2_zfmisc_1(A_648,B_649)))
      | ~ v1_funct_1(E_650) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_8358])).

tff(c_8495,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_88,c_8483])).

tff(c_8503,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_2694,c_8495])).

tff(c_8505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8164,c_8503])).

tff(c_8506,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_8071])).

tff(c_8523,plain,
    ( k2_relat_1('#skF_4') = k1_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8506,c_22])).

tff(c_8531,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_86,c_4599,c_5216,c_8523])).

tff(c_76,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_235])).

tff(c_7393,plain,(
    ! [B_556] :
      ( k2_funct_1('#skF_3') = B_556
      | k5_relat_1(B_556,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_556) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_7367])).

tff(c_7401,plain,(
    ! [B_556] :
      ( k2_funct_1('#skF_3') = B_556
      | k5_relat_1(B_556,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_556) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_556)
      | ~ v1_relat_1(B_556) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147,c_92,c_76,c_7393])).

tff(c_8653,plain,(
    ! [B_656] :
      ( k2_funct_1('#skF_3') = B_656
      | k5_relat_1(B_656,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_656) != '#skF_1'
      | ~ v1_funct_1(B_656)
      | ~ v1_relat_1(B_656) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8531,c_7401])).

tff(c_8659,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_8653])).

tff(c_8671,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_5216,c_8659])).

tff(c_8672,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_8671])).

tff(c_9087,plain,(
    ! [A_692,C_693,B_694] :
      ( k6_partfun1(A_692) = k5_relat_1(C_693,k2_funct_1(C_693))
      | k1_xboole_0 = B_694
      | ~ v2_funct_1(C_693)
      | k2_relset_1(A_692,B_694,C_693) != B_694
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_692,B_694)))
      | ~ v1_funct_2(C_693,A_692,B_694)
      | ~ v1_funct_1(C_693) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_9093,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_82,c_9087])).

tff(c_9102,plain,
    ( k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_84,c_5217,c_4599,c_8506,c_9093])).

tff(c_9104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_8672,c_9102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:56:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.15/3.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.24  
% 9.15/3.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.24  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.15/3.24  
% 9.15/3.24  %Foreground sorts:
% 9.15/3.24  
% 9.15/3.24  
% 9.15/3.24  %Background operators:
% 9.15/3.24  
% 9.15/3.24  
% 9.15/3.24  %Foreground operators:
% 9.15/3.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 9.15/3.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.15/3.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 9.15/3.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 9.15/3.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.15/3.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 9.15/3.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.15/3.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.15/3.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.15/3.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.15/3.24  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 9.15/3.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.15/3.24  tff('#skF_2', type, '#skF_2': $i).
% 9.15/3.24  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 9.15/3.24  tff('#skF_3', type, '#skF_3': $i).
% 9.15/3.24  tff('#skF_1', type, '#skF_1': $i).
% 9.15/3.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.15/3.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.15/3.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 9.15/3.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.15/3.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.15/3.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.15/3.24  tff('#skF_4', type, '#skF_4': $i).
% 9.15/3.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.15/3.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.15/3.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.15/3.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.15/3.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.15/3.24  
% 9.15/3.27  tff(f_235, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 9.15/3.27  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 9.15/3.27  tff(f_193, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 9.15/3.27  tff(f_134, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 9.15/3.27  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 9.15/3.27  tff(f_132, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 9.15/3.27  tff(f_122, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 9.15/3.27  tff(f_106, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 9.15/3.27  tff(f_118, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 9.15/3.27  tff(f_177, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 9.15/3.27  tff(f_88, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.15/3.27  tff(f_94, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.15/3.27  tff(f_53, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 9.15/3.27  tff(f_38, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.15/3.27  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(A), k2_relat_1(B)) => (k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_relat_1)).
% 9.15/3.27  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 9.15/3.27  tff(f_67, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 9.15/3.27  tff(f_209, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 9.15/3.27  tff(c_74, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_70, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_86, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_84, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_82, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_278, plain, (![A_100, B_101, C_102]: (k2_relset_1(A_100, B_101, C_102)=k2_relat_1(C_102) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 9.15/3.27  tff(c_290, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_278])).
% 9.15/3.27  tff(c_2808, plain, (![C_294, A_295, B_296]: (v1_funct_1(k2_funct_1(C_294)) | k2_relset_1(A_295, B_296, C_294)!=B_296 | ~v2_funct_1(C_294) | ~m1_subset_1(C_294, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_2(C_294, A_295, B_296) | ~v1_funct_1(C_294))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.15/3.27  tff(c_2814, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_2808])).
% 9.15/3.27  tff(c_2823, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_290, c_2814])).
% 9.15/3.27  tff(c_2827, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2823])).
% 9.15/3.27  tff(c_92, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_90, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_88, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_48, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_134])).
% 9.15/3.27  tff(c_18, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.15/3.27  tff(c_94, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 9.15/3.27  tff(c_80, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_2330, plain, (![B_261, A_260, E_264, F_262, C_265, D_263]: (k1_partfun1(A_260, B_261, C_265, D_263, E_264, F_262)=k5_relat_1(E_264, F_262) | ~m1_subset_1(F_262, k1_zfmisc_1(k2_zfmisc_1(C_265, D_263))) | ~v1_funct_1(F_262) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~v1_funct_1(E_264))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.15/3.27  tff(c_2336, plain, (![A_260, B_261, E_264]: (k1_partfun1(A_260, B_261, '#skF_2', '#skF_1', E_264, '#skF_4')=k5_relat_1(E_264, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))) | ~v1_funct_1(E_264))), inference(resolution, [status(thm)], [c_82, c_2330])).
% 9.15/3.27  tff(c_2350, plain, (![A_270, B_271, E_272]: (k1_partfun1(A_270, B_271, '#skF_2', '#skF_1', E_272, '#skF_4')=k5_relat_1(E_272, '#skF_4') | ~m1_subset_1(E_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_1(E_272))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_2336])).
% 9.15/3.27  tff(c_2362, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_2350])).
% 9.15/3.27  tff(c_2370, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2362])).
% 9.15/3.27  tff(c_44, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_122])).
% 9.15/3.27  tff(c_78, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_486, plain, (![D_115, C_116, A_117, B_118]: (D_115=C_116 | ~r2_relset_1(A_117, B_118, C_116, D_115) | ~m1_subset_1(D_115, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~m1_subset_1(C_116, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))))), inference(cnfTransformation, [status(thm)], [f_106])).
% 9.15/3.27  tff(c_494, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_78, c_486])).
% 9.15/3.27  tff(c_509, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_494])).
% 9.15/3.27  tff(c_696, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_509])).
% 9.15/3.27  tff(c_2377, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2370, c_696])).
% 9.15/3.27  tff(c_2605, plain, (![A_288, E_289, B_286, C_285, D_290, F_287]: (m1_subset_1(k1_partfun1(A_288, B_286, C_285, D_290, E_289, F_287), k1_zfmisc_1(k2_zfmisc_1(A_288, D_290))) | ~m1_subset_1(F_287, k1_zfmisc_1(k2_zfmisc_1(C_285, D_290))) | ~v1_funct_1(F_287) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_288, B_286))) | ~v1_funct_1(E_289))), inference(cnfTransformation, [status(thm)], [f_118])).
% 9.15/3.27  tff(c_2662, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2370, c_2605])).
% 9.15/3.27  tff(c_2691, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_88, c_86, c_82, c_2662])).
% 9.15/3.27  tff(c_2693, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2377, c_2691])).
% 9.15/3.27  tff(c_2694, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_509])).
% 9.15/3.27  tff(c_4581, plain, (![D_393, E_389, A_392, C_390, B_391]: (k1_xboole_0=C_390 | v2_funct_1(E_389) | k2_relset_1(A_392, B_391, D_393)!=B_391 | ~v2_funct_1(k1_partfun1(A_392, B_391, B_391, C_390, D_393, E_389)) | ~m1_subset_1(E_389, k1_zfmisc_1(k2_zfmisc_1(B_391, C_390))) | ~v1_funct_2(E_389, B_391, C_390) | ~v1_funct_1(E_389) | ~m1_subset_1(D_393, k1_zfmisc_1(k2_zfmisc_1(A_392, B_391))) | ~v1_funct_2(D_393, A_392, B_391) | ~v1_funct_1(D_393))), inference(cnfTransformation, [status(thm)], [f_177])).
% 9.15/3.27  tff(c_4587, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2694, c_4581])).
% 9.15/3.27  tff(c_4595, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_90, c_88, c_86, c_84, c_82, c_94, c_80, c_4587])).
% 9.15/3.27  tff(c_4597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2827, c_74, c_4595])).
% 9.15/3.27  tff(c_4598, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2823])).
% 9.15/3.27  tff(c_4600, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4598])).
% 9.15/3.27  tff(c_134, plain, (![C_71, A_72, B_73]: (v1_relat_1(C_71) | ~m1_subset_1(C_71, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.15/3.27  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_134])).
% 9.15/3.27  tff(c_203, plain, (![C_88, A_89, B_90]: (v4_relat_1(C_88, A_89) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_89, B_90))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 9.15/3.27  tff(c_214, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_82, c_203])).
% 9.15/3.27  tff(c_14, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.15/3.27  tff(c_96, plain, (![A_11]: (k2_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 9.15/3.27  tff(c_5169, plain, (![C_439, B_435, A_434, D_437, F_436, E_438]: (k1_partfun1(A_434, B_435, C_439, D_437, E_438, F_436)=k5_relat_1(E_438, F_436) | ~m1_subset_1(F_436, k1_zfmisc_1(k2_zfmisc_1(C_439, D_437))) | ~v1_funct_1(F_436) | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))) | ~v1_funct_1(E_438))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.15/3.27  tff(c_5173, plain, (![A_434, B_435, E_438]: (k1_partfun1(A_434, B_435, '#skF_2', '#skF_1', E_438, '#skF_4')=k5_relat_1(E_438, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_438, k1_zfmisc_1(k2_zfmisc_1(A_434, B_435))) | ~v1_funct_1(E_438))), inference(resolution, [status(thm)], [c_82, c_5169])).
% 9.15/3.27  tff(c_5183, plain, (![A_440, B_441, E_442]: (k1_partfun1(A_440, B_441, '#skF_2', '#skF_1', E_442, '#skF_4')=k5_relat_1(E_442, '#skF_4') | ~m1_subset_1(E_442, k1_zfmisc_1(k2_zfmisc_1(A_440, B_441))) | ~v1_funct_1(E_442))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5173])).
% 9.15/3.27  tff(c_5192, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_5183])).
% 9.15/3.27  tff(c_5199, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2694, c_5192])).
% 9.15/3.27  tff(c_6, plain, (![B_5, A_4]: (r1_tarski(k1_relat_1(B_5), A_4) | ~v4_relat_1(B_5, A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.15/3.27  tff(c_147, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_134])).
% 9.15/3.27  tff(c_287, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_278])).
% 9.15/3.27  tff(c_292, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_287])).
% 9.15/3.27  tff(c_10, plain, (![B_10, A_8]: (k2_relat_1(k5_relat_1(B_10, A_8))=k2_relat_1(A_8) | ~r1_tarski(k1_relat_1(A_8), k2_relat_1(B_10)) | ~v1_relat_1(B_10) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.15/3.27  tff(c_318, plain, (![A_8]: (k2_relat_1(k5_relat_1('#skF_3', A_8))=k2_relat_1(A_8) | ~r1_tarski(k1_relat_1(A_8), '#skF_2') | ~v1_relat_1('#skF_3') | ~v1_relat_1(A_8))), inference(superposition, [status(thm), theory('equality')], [c_292, c_10])).
% 9.15/3.27  tff(c_337, plain, (![A_106]: (k2_relat_1(k5_relat_1('#skF_3', A_106))=k2_relat_1(A_106) | ~r1_tarski(k1_relat_1(A_106), '#skF_2') | ~v1_relat_1(A_106))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_318])).
% 9.15/3.27  tff(c_348, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_3', B_5))=k2_relat_1(B_5) | ~v4_relat_1(B_5, '#skF_2') | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_337])).
% 9.15/3.27  tff(c_5206, plain, (k2_relat_1(k6_partfun1('#skF_1'))=k2_relat_1('#skF_4') | ~v4_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5199, c_348])).
% 9.15/3.27  tff(c_5212, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_214, c_96, c_5206])).
% 9.15/3.27  tff(c_5214, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4600, c_5212])).
% 9.15/3.27  tff(c_5216, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4598])).
% 9.15/3.27  tff(c_4599, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2823])).
% 9.15/3.27  tff(c_24, plain, (![A_14, B_16]: (k2_funct_1(A_14)=B_16 | k6_relat_1(k2_relat_1(A_14))!=k5_relat_1(B_16, A_14) | k2_relat_1(B_16)!=k1_relat_1(A_14) | ~v2_funct_1(A_14) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.15/3.27  tff(c_7367, plain, (![A_555, B_556]: (k2_funct_1(A_555)=B_556 | k6_partfun1(k2_relat_1(A_555))!=k5_relat_1(B_556, A_555) | k2_relat_1(B_556)!=k1_relat_1(A_555) | ~v2_funct_1(A_555) | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~v1_funct_1(A_555) | ~v1_relat_1(A_555))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_24])).
% 9.15/3.27  tff(c_7375, plain, (![B_556]: (k2_funct_1('#skF_4')=B_556 | k5_relat_1(B_556, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_556)!=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5216, c_7367])).
% 9.15/3.27  tff(c_7404, plain, (![B_557]: (k2_funct_1('#skF_4')=B_557 | k5_relat_1(B_557, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_557)!=k1_relat_1('#skF_4') | ~v1_funct_1(B_557) | ~v1_relat_1(B_557))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_4599, c_7375])).
% 9.15/3.27  tff(c_7410, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_147, c_7404])).
% 9.15/3.27  tff(c_7426, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k1_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_292, c_7410])).
% 9.15/3.27  tff(c_7433, plain, (k1_relat_1('#skF_4')!='#skF_2'), inference(splitLeft, [status(thm)], [c_7426])).
% 9.15/3.27  tff(c_22, plain, (![A_13]: (k1_relat_1(k2_funct_1(A_13))=k2_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.15/3.27  tff(c_231, plain, (![A_92]: (v4_relat_1(k6_partfun1(A_92), A_92))), inference(resolution, [status(thm)], [c_44, c_203])).
% 9.15/3.27  tff(c_16, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.15/3.27  tff(c_95, plain, (![A_12]: (v1_relat_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 9.15/3.27  tff(c_12, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.15/3.27  tff(c_97, plain, (![A_11]: (k1_relat_1(k6_partfun1(A_11))=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 9.15/3.27  tff(c_167, plain, (![B_76, A_77]: (r1_tarski(k1_relat_1(B_76), A_77) | ~v4_relat_1(B_76, A_77) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.15/3.27  tff(c_170, plain, (![A_11, A_77]: (r1_tarski(A_11, A_77) | ~v4_relat_1(k6_partfun1(A_11), A_77) | ~v1_relat_1(k6_partfun1(A_11)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_167])).
% 9.15/3.27  tff(c_172, plain, (![A_11, A_77]: (r1_tarski(A_11, A_77) | ~v4_relat_1(k6_partfun1(A_11), A_77))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_170])).
% 9.15/3.27  tff(c_236, plain, (![A_93]: (r1_tarski(A_93, A_93))), inference(resolution, [status(thm)], [c_231, c_172])).
% 9.15/3.27  tff(c_4, plain, (![B_5, A_4]: (v4_relat_1(B_5, A_4) | ~r1_tarski(k1_relat_1(B_5), A_4) | ~v1_relat_1(B_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.15/3.27  tff(c_242, plain, (![B_94]: (v4_relat_1(B_94, k1_relat_1(B_94)) | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_236, c_4])).
% 9.15/3.27  tff(c_249, plain, (![A_13]: (v4_relat_1(k2_funct_1(A_13), k2_relat_1(A_13)) | ~v1_relat_1(k2_funct_1(A_13)) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_22, c_242])).
% 9.15/3.27  tff(c_5221, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5216, c_249])).
% 9.15/3.27  tff(c_5234, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_4599, c_5221])).
% 9.15/3.27  tff(c_5275, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5234])).
% 9.15/3.27  tff(c_5217, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5216, c_290])).
% 9.15/3.27  tff(c_5641, plain, (![C_481, B_482, A_483]: (m1_subset_1(k2_funct_1(C_481), k1_zfmisc_1(k2_zfmisc_1(B_482, A_483))) | k2_relset_1(A_483, B_482, C_481)!=B_482 | ~v2_funct_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_483, B_482))) | ~v1_funct_2(C_481, A_483, B_482) | ~v1_funct_1(C_481))), inference(cnfTransformation, [status(thm)], [f_193])).
% 9.15/3.27  tff(c_26, plain, (![C_19, A_17, B_18]: (v1_relat_1(C_19) | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.15/3.27  tff(c_7152, plain, (![C_547, A_548, B_549]: (v1_relat_1(k2_funct_1(C_547)) | k2_relset_1(A_548, B_549, C_547)!=B_549 | ~v2_funct_1(C_547) | ~m1_subset_1(C_547, k1_zfmisc_1(k2_zfmisc_1(A_548, B_549))) | ~v1_funct_2(C_547, A_548, B_549) | ~v1_funct_1(C_547))), inference(resolution, [status(thm)], [c_5641, c_26])).
% 9.15/3.27  tff(c_7185, plain, (v1_relat_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_7152])).
% 9.15/3.27  tff(c_7217, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_4599, c_5217, c_7185])).
% 9.15/3.27  tff(c_7219, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5275, c_7217])).
% 9.15/3.27  tff(c_7221, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5234])).
% 9.15/3.27  tff(c_7220, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_5234])).
% 9.15/3.27  tff(c_7993, plain, (![A_610, C_611, B_612]: (k6_partfun1(A_610)=k5_relat_1(C_611, k2_funct_1(C_611)) | k1_xboole_0=B_612 | ~v2_funct_1(C_611) | k2_relset_1(A_610, B_612, C_611)!=B_612 | ~m1_subset_1(C_611, k1_zfmisc_1(k2_zfmisc_1(A_610, B_612))) | ~v1_funct_2(C_611, A_610, B_612) | ~v1_funct_1(C_611))), inference(cnfTransformation, [status(thm)], [f_209])).
% 9.15/3.27  tff(c_7999, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_7993])).
% 9.15/3.27  tff(c_8008, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_5217, c_4599, c_7999])).
% 9.15/3.27  tff(c_8009, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_74, c_8008])).
% 9.15/3.27  tff(c_293, plain, (![B_103, A_104]: (k2_relat_1(k5_relat_1(B_103, A_104))=k2_relat_1(A_104) | ~r1_tarski(k1_relat_1(A_104), k2_relat_1(B_103)) | ~v1_relat_1(B_103) | ~v1_relat_1(A_104))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.15/3.27  tff(c_310, plain, (![B_103, B_5]: (k2_relat_1(k5_relat_1(B_103, B_5))=k2_relat_1(B_5) | ~v1_relat_1(B_103) | ~v4_relat_1(B_5, k2_relat_1(B_103)) | ~v1_relat_1(B_5))), inference(resolution, [status(thm)], [c_6, c_293])).
% 9.15/3.27  tff(c_5227, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_4', B_5))=k2_relat_1(B_5) | ~v1_relat_1('#skF_4') | ~v4_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(superposition, [status(thm), theory('equality')], [c_5216, c_310])).
% 9.15/3.27  tff(c_5238, plain, (![B_5]: (k2_relat_1(k5_relat_1('#skF_4', B_5))=k2_relat_1(B_5) | ~v4_relat_1(B_5, '#skF_1') | ~v1_relat_1(B_5))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_5227])).
% 9.15/3.27  tff(c_8020, plain, (k2_relat_1(k6_partfun1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_4')) | ~v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8009, c_5238])).
% 9.15/3.27  tff(c_8026, plain, (k2_relat_1(k2_funct_1('#skF_4'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7221, c_7220, c_96, c_8020])).
% 9.15/3.27  tff(c_20, plain, (![A_13]: (k2_relat_1(k2_funct_1(A_13))=k1_relat_1(A_13) | ~v2_funct_1(A_13) | ~v1_funct_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.15/3.27  tff(c_8049, plain, (k1_relat_1('#skF_4')='#skF_2' | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8026, c_20])).
% 9.15/3.27  tff(c_8068, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_4599, c_8049])).
% 9.15/3.27  tff(c_8070, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7433, c_8068])).
% 9.15/3.27  tff(c_8071, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_7426])).
% 9.15/3.27  tff(c_8164, plain, (k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_8071])).
% 9.15/3.27  tff(c_8354, plain, (![D_634, C_636, F_633, E_635, A_631, B_632]: (k1_partfun1(A_631, B_632, C_636, D_634, E_635, F_633)=k5_relat_1(E_635, F_633) | ~m1_subset_1(F_633, k1_zfmisc_1(k2_zfmisc_1(C_636, D_634))) | ~v1_funct_1(F_633) | ~m1_subset_1(E_635, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))) | ~v1_funct_1(E_635))), inference(cnfTransformation, [status(thm)], [f_132])).
% 9.15/3.27  tff(c_8358, plain, (![A_631, B_632, E_635]: (k1_partfun1(A_631, B_632, '#skF_2', '#skF_1', E_635, '#skF_4')=k5_relat_1(E_635, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_635, k1_zfmisc_1(k2_zfmisc_1(A_631, B_632))) | ~v1_funct_1(E_635))), inference(resolution, [status(thm)], [c_82, c_8354])).
% 9.15/3.27  tff(c_8483, plain, (![A_648, B_649, E_650]: (k1_partfun1(A_648, B_649, '#skF_2', '#skF_1', E_650, '#skF_4')=k5_relat_1(E_650, '#skF_4') | ~m1_subset_1(E_650, k1_zfmisc_1(k2_zfmisc_1(A_648, B_649))) | ~v1_funct_1(E_650))), inference(demodulation, [status(thm), theory('equality')], [c_86, c_8358])).
% 9.15/3.27  tff(c_8495, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_88, c_8483])).
% 9.15/3.27  tff(c_8503, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_2694, c_8495])).
% 9.15/3.27  tff(c_8505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8164, c_8503])).
% 9.15/3.27  tff(c_8506, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_8071])).
% 9.15/3.27  tff(c_8523, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8506, c_22])).
% 9.15/3.27  tff(c_8531, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_86, c_4599, c_5216, c_8523])).
% 9.15/3.27  tff(c_76, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_235])).
% 9.15/3.27  tff(c_7393, plain, (![B_556]: (k2_funct_1('#skF_3')=B_556 | k5_relat_1(B_556, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_556)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_556) | ~v1_relat_1(B_556) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_292, c_7367])).
% 9.15/3.27  tff(c_7401, plain, (![B_556]: (k2_funct_1('#skF_3')=B_556 | k5_relat_1(B_556, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_556)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_556) | ~v1_relat_1(B_556))), inference(demodulation, [status(thm), theory('equality')], [c_147, c_92, c_76, c_7393])).
% 9.15/3.27  tff(c_8653, plain, (![B_656]: (k2_funct_1('#skF_3')=B_656 | k5_relat_1(B_656, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_656)!='#skF_1' | ~v1_funct_1(B_656) | ~v1_relat_1(B_656))), inference(demodulation, [status(thm), theory('equality')], [c_8531, c_7401])).
% 9.15/3.27  tff(c_8659, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!='#skF_1' | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_8653])).
% 9.15/3.27  tff(c_8671, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_5216, c_8659])).
% 9.15/3.27  tff(c_8672, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_70, c_8671])).
% 9.15/3.27  tff(c_9087, plain, (![A_692, C_693, B_694]: (k6_partfun1(A_692)=k5_relat_1(C_693, k2_funct_1(C_693)) | k1_xboole_0=B_694 | ~v2_funct_1(C_693) | k2_relset_1(A_692, B_694, C_693)!=B_694 | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_692, B_694))) | ~v1_funct_2(C_693, A_692, B_694) | ~v1_funct_1(C_693))), inference(cnfTransformation, [status(thm)], [f_209])).
% 9.15/3.27  tff(c_9093, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_82, c_9087])).
% 9.15/3.27  tff(c_9102, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_86, c_84, c_5217, c_4599, c_8506, c_9093])).
% 9.15/3.27  tff(c_9104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_8672, c_9102])).
% 9.15/3.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.15/3.27  
% 9.15/3.27  Inference rules
% 9.15/3.27  ----------------------
% 9.15/3.27  #Ref     : 0
% 9.15/3.27  #Sup     : 2028
% 9.15/3.27  #Fact    : 0
% 9.15/3.27  #Define  : 0
% 9.15/3.27  #Split   : 52
% 9.15/3.27  #Chain   : 0
% 9.15/3.27  #Close   : 0
% 9.15/3.27  
% 9.15/3.27  Ordering : KBO
% 9.15/3.27  
% 9.15/3.27  Simplification rules
% 9.15/3.27  ----------------------
% 9.15/3.27  #Subsume      : 171
% 9.15/3.27  #Demod        : 2052
% 9.15/3.27  #Tautology    : 525
% 9.15/3.27  #SimpNegUnit  : 70
% 9.15/3.27  #BackRed      : 38
% 9.15/3.27  
% 9.15/3.27  #Partial instantiations: 0
% 9.15/3.27  #Strategies tried      : 1
% 9.15/3.27  
% 9.15/3.27  Timing (in seconds)
% 9.15/3.27  ----------------------
% 9.15/3.27  Preprocessing        : 0.39
% 9.15/3.27  Parsing              : 0.20
% 9.15/3.27  CNF conversion       : 0.03
% 9.15/3.27  Main loop            : 2.03
% 9.15/3.27  Inferencing          : 0.67
% 9.15/3.27  Reduction            : 0.77
% 9.15/3.27  Demodulation         : 0.57
% 9.15/3.27  BG Simplification    : 0.09
% 9.15/3.27  Subsumption          : 0.38
% 9.15/3.27  Abstraction          : 0.09
% 9.15/3.27  MUC search           : 0.00
% 9.15/3.27  Cooper               : 0.00
% 9.15/3.27  Total                : 2.47
% 9.15/3.27  Index Insertion      : 0.00
% 9.15/3.27  Index Deletion       : 0.00
% 9.15/3.27  Index Matching       : 0.00
% 9.15/3.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
