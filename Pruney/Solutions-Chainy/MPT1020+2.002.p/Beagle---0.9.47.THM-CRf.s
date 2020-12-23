%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:50 EST 2020

% Result     : Theorem 48.81s
% Output     : CNFRefutation 49.26s
% Verified   : 
% Statistics : Number of formulae       :  367 (31697 expanded)
%              Number of leaves         :   75 (10276 expanded)
%              Depth                    :   24
%              Number of atoms          :  835 (90020 expanded)
%              Number of equality atoms :  204 (5809 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v5_funct_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k8_setfam_1 > k6_setfam_1 > k5_relat_1 > k3_subset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(np__1,type,(
    np__1: $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_funct_2,type,(
    k2_funct_2: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v5_funct_1,type,(
    v5_funct_1: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(v5_ordinal1,type,(
    v5_ordinal1: $i > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff(v2_funct_2,type,(
    v2_funct_2: ( $i * $i ) > $o )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v3_funct_2,type,(
    v3_funct_2: ( $i * $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( ! [D] :
                ( m1_subset_1(D,A)
               => ( r2_hidden(D,B)
                 => r2_hidden(D,C) ) )
           => r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

tff(f_439,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & v3_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & v3_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,B,C),k6_partfun1(A))
             => r2_relset_1(A,A,C,k2_funct_2(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_funct_2)).

tff(f_197,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_209,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_201,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_248,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v3_funct_2(C,A,B) )
       => ( v1_funct_1(C)
          & v2_funct_1(C)
          & v2_funct_2(C,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_funct_2)).

tff(f_392,axiom,(
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

tff(f_336,axiom,(
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

tff(f_71,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_309,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_xboole_0(C)
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_relset_1)).

tff(f_190,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A)
          & k2_relat_1(k5_relat_1(k2_funct_1(A),A)) = k2_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_funct_1)).

tff(f_298,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_278,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_357,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
              & v2_funct_1(E) )
           => ( C = k1_xboole_0
              | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_417,axiom,(
    ! [A,B,C] :
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

tff(f_319,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & v3_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k2_funct_2(A,B) = k2_funct_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_funct_2)).

tff(f_102,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( v1_xboole_0(B)
           => v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_subset_1)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_106,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => ( ( r1_tarski(B,C)
          & r1_tarski(B,k3_subset_1(A,C)) )
       => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_294,axiom,(
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

tff(f_217,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_relset_1)).

tff(f_266,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_236,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_229,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_10,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_137154,plain,(
    ! [A_5452,B_5453,C_5454] :
      ( r2_hidden('#skF_1'(A_5452,B_5453,C_5454),B_5453)
      | r1_tarski(B_5453,C_5454)
      | ~ m1_subset_1(C_5454,k1_zfmisc_1(A_5452))
      | ~ m1_subset_1(B_5453,k1_zfmisc_1(A_5452)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_154,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_486,plain,(
    ! [C_202,B_203,A_204] :
      ( v1_xboole_0(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(B_203,A_204)))
      | ~ v1_xboole_0(A_204) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_519,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_486])).

tff(c_524,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_737,plain,(
    ! [A_240,B_241,D_242] :
      ( r2_relset_1(A_240,B_241,D_242,D_242)
      | ~ m1_subset_1(D_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241))) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_769,plain,(
    r2_relset_1('#skF_5','#skF_5','#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_737])).

tff(c_160,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_158,plain,(
    v1_funct_2('#skF_7','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_823,plain,(
    ! [A_255,B_256,C_257] :
      ( k2_relset_1(A_255,B_256,C_257) = k2_relat_1(C_257)
      | ~ m1_subset_1(C_257,k1_zfmisc_1(k2_zfmisc_1(A_255,B_256))) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_865,plain,(
    k2_relset_1('#skF_5','#skF_5','#skF_7') = k2_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_823])).

tff(c_156,plain,(
    v3_funct_2('#skF_7','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_1331,plain,(
    ! [C_314,A_315,B_316] :
      ( v2_funct_1(C_314)
      | ~ v3_funct_2(C_314,A_315,B_316)
      | ~ v1_funct_1(C_314)
      | ~ m1_subset_1(C_314,k1_zfmisc_1(k2_zfmisc_1(A_315,B_316))) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_1355,plain,
    ( v2_funct_1('#skF_7')
    | ~ v3_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_1331])).

tff(c_1375,plain,(
    v2_funct_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_156,c_1355])).

tff(c_12515,plain,(
    ! [B_774,C_775,A_776] :
      ( k6_partfun1(B_774) = k5_relat_1(k2_funct_1(C_775),C_775)
      | k1_xboole_0 = B_774
      | ~ v2_funct_1(C_775)
      | k2_relset_1(A_776,B_774,C_775) != B_774
      | ~ m1_subset_1(C_775,k1_zfmisc_1(k2_zfmisc_1(A_776,B_774)))
      | ~ v1_funct_2(C_775,A_776,B_774)
      | ~ v1_funct_1(C_775) ) ),
    inference(cnfTransformation,[status(thm)],[f_392])).

tff(c_12550,plain,
    ( k5_relat_1(k2_funct_1('#skF_7'),'#skF_7') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_7')
    | k2_relset_1('#skF_5','#skF_5','#skF_7') != '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_12515])).

tff(c_12583,plain,
    ( k5_relat_1(k2_funct_1('#skF_7'),'#skF_7') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | k2_relat_1('#skF_7') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_158,c_865,c_1375,c_12550])).

tff(c_12726,plain,(
    k2_relat_1('#skF_7') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12583])).

tff(c_168,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_166,plain,(
    v1_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_162,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_152,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k6_partfun1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_13112,plain,(
    ! [A_793,B_794,C_795,D_796] :
      ( k2_relset_1(A_793,B_794,C_795) = B_794
      | ~ r2_relset_1(B_794,B_794,k1_partfun1(B_794,A_793,A_793,B_794,D_796,C_795),k6_partfun1(B_794))
      | ~ m1_subset_1(D_796,k1_zfmisc_1(k2_zfmisc_1(B_794,A_793)))
      | ~ v1_funct_2(D_796,B_794,A_793)
      | ~ v1_funct_1(D_796)
      | ~ m1_subset_1(C_795,k1_zfmisc_1(k2_zfmisc_1(A_793,B_794)))
      | ~ v1_funct_2(C_795,A_793,B_794)
      | ~ v1_funct_1(C_795) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_13115,plain,
    ( k2_relset_1('#skF_5','#skF_5','#skF_7') = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_152,c_13112])).

tff(c_13118,plain,(
    k2_relat_1('#skF_7') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_158,c_154,c_168,c_166,c_162,c_865,c_13115])).

tff(c_13120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12726,c_13118])).

tff(c_13122,plain,(
    k2_relat_1('#skF_7') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12583])).

tff(c_12389,plain,(
    ! [A_771,C_772,B_773] :
      ( k6_partfun1(A_771) = k5_relat_1(C_772,k2_funct_1(C_772))
      | k1_xboole_0 = B_773
      | ~ v2_funct_1(C_772)
      | k2_relset_1(A_771,B_773,C_772) != B_773
      | ~ m1_subset_1(C_772,k1_zfmisc_1(k2_zfmisc_1(A_771,B_773)))
      | ~ v1_funct_2(C_772,A_771,B_773)
      | ~ v1_funct_1(C_772) ) ),
    inference(cnfTransformation,[status(thm)],[f_392])).

tff(c_12424,plain,
    ( k5_relat_1('#skF_7',k2_funct_1('#skF_7')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_7')
    | k2_relset_1('#skF_5','#skF_5','#skF_7') != '#skF_5'
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_12389])).

tff(c_12457,plain,
    ( k5_relat_1('#skF_7',k2_funct_1('#skF_7')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | k2_relat_1('#skF_7') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_158,c_865,c_1375,c_12424])).

tff(c_14724,plain,
    ( k5_relat_1('#skF_7',k2_funct_1('#skF_7')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13122,c_12457])).

tff(c_14725,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_14724])).

tff(c_249,plain,(
    ! [B_155,A_156] :
      ( v1_xboole_0(B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156))
      | ~ v1_xboole_0(A_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_277,plain,(
    ! [A_10] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_10) ) ),
    inference(resolution,[status(thm)],[c_10,c_249])).

tff(c_278,plain,(
    ! [A_10] : ~ v1_xboole_0(A_10) ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_130,plain,(
    ! [A_94,B_95] : v1_xboole_0('#skF_4'(A_94,B_95)) ),
    inference(cnfTransformation,[status(thm)],[f_309])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_278,c_130])).

tff(c_282,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_14787,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14725,c_282])).

tff(c_14800,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_14787])).

tff(c_14802,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_14724])).

tff(c_867,plain,(
    k2_relset_1('#skF_5','#skF_5','#skF_6') = k2_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_823])).

tff(c_164,plain,(
    v3_funct_2('#skF_6','#skF_5','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_1362,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_1331])).

tff(c_1379,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_164,c_1362])).

tff(c_12555,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_12515])).

tff(c_12587,plain,
    ( k5_relat_1(k2_funct_1('#skF_6'),'#skF_6') = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_867,c_1379,c_12555])).

tff(c_13133,plain,(
    k2_relat_1('#skF_6') != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_12587])).

tff(c_321,plain,(
    ! [C_162,A_163,B_164] :
      ( v1_relat_1(C_162)
      | ~ m1_subset_1(C_162,k1_zfmisc_1(k2_zfmisc_1(A_163,B_164))) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_354,plain,(
    v1_relat_1('#skF_7') ),
    inference(resolution,[status(thm)],[c_154,c_321])).

tff(c_13121,plain,
    ( k1_xboole_0 = '#skF_5'
    | k5_relat_1(k2_funct_1('#skF_7'),'#skF_7') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_12583])).

tff(c_13132,plain,(
    k5_relat_1(k2_funct_1('#skF_7'),'#skF_7') = k6_partfun1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_13121])).

tff(c_52,plain,(
    ! [A_48] :
      ( k2_relat_1(k5_relat_1(k2_funct_1(A_48),A_48)) = k2_relat_1(A_48)
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_13143,plain,
    ( k2_relat_1(k6_partfun1('#skF_5')) = k2_relat_1('#skF_7')
    | ~ v2_funct_1('#skF_7')
    | ~ v1_funct_1('#skF_7')
    | ~ v1_relat_1('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_13132,c_52])).

tff(c_13154,plain,(
    k2_relat_1(k6_partfun1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_160,c_1375,c_13122,c_13143])).

tff(c_122,plain,(
    ! [A_93] : m1_subset_1(k6_partfun1(A_93),k1_zfmisc_1(k2_zfmisc_1(A_93,A_93))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_864,plain,(
    ! [A_93] : k2_relset_1(A_93,A_93,k6_partfun1(A_93)) = k2_relat_1(k6_partfun1(A_93)) ),
    inference(resolution,[status(thm)],[c_122,c_823])).

tff(c_108,plain,(
    ! [A_85,D_88,F_90,C_87,E_89,B_86] :
      ( m1_subset_1(k1_partfun1(A_85,B_86,C_87,D_88,E_89,F_90),k1_zfmisc_1(k2_zfmisc_1(A_85,D_88)))
      | ~ m1_subset_1(F_90,k1_zfmisc_1(k2_zfmisc_1(C_87,D_88)))
      | ~ v1_funct_1(F_90)
      | ~ m1_subset_1(E_89,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86)))
      | ~ v1_funct_1(E_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_10742,plain,(
    ! [D_724,C_725,A_726,B_727] :
      ( D_724 = C_725
      | ~ r2_relset_1(A_726,B_727,C_725,D_724)
      | ~ m1_subset_1(D_724,k1_zfmisc_1(k2_zfmisc_1(A_726,B_727)))
      | ~ m1_subset_1(C_725,k1_zfmisc_1(k2_zfmisc_1(A_726,B_727))) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_10760,plain,
    ( k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_152,c_10742])).

tff(c_10795,plain,
    ( k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_10760])).

tff(c_15189,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_10795])).

tff(c_15629,plain,
    ( ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_15189])).

tff(c_15636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_162,c_160,c_154,c_15629])).

tff(c_15637,plain,(
    k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_10795])).

tff(c_138,plain,(
    ! [D_107,A_104,C_106,B_105,E_109] :
      ( k2_relset_1(A_104,B_105,D_107) = B_105
      | k1_xboole_0 = C_106
      | ~ v2_funct_1(E_109)
      | k2_relset_1(A_104,C_106,k1_partfun1(A_104,B_105,B_105,C_106,D_107,E_109)) != C_106
      | ~ m1_subset_1(E_109,k1_zfmisc_1(k2_zfmisc_1(B_105,C_106)))
      | ~ v1_funct_2(E_109,B_105,C_106)
      | ~ v1_funct_1(E_109)
      | ~ m1_subset_1(D_107,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105)))
      | ~ v1_funct_2(D_107,A_104,B_105)
      | ~ v1_funct_1(D_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_357])).

tff(c_15663,plain,
    ( k2_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_7')
    | k2_relset_1('#skF_5','#skF_5',k6_partfun1('#skF_5')) != '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_15637,c_138])).

tff(c_15682,plain,
    ( k2_relat_1('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_162,c_160,c_158,c_154,c_13154,c_864,c_1375,c_867,c_15663])).

tff(c_15684,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14802,c_13133,c_15682])).

tff(c_15686,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12587])).

tff(c_12429,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_12389])).

tff(c_12461,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5'
    | k2_relat_1('#skF_6') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_867,c_1379,c_12429])).

tff(c_15753,plain,
    ( k5_relat_1('#skF_6',k2_funct_1('#skF_6')) = k6_partfun1('#skF_5')
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15686,c_12461])).

tff(c_15754,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_15753])).

tff(c_15815,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15754,c_282])).

tff(c_15826,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_15815])).

tff(c_15828,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_15753])).

tff(c_15687,plain,(
    k2_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15686,c_867])).

tff(c_16313,plain,(
    ! [C_890,D_891,B_892,A_893] :
      ( k2_funct_1(C_890) = D_891
      | k1_xboole_0 = B_892
      | k1_xboole_0 = A_893
      | ~ v2_funct_1(C_890)
      | ~ r2_relset_1(A_893,A_893,k1_partfun1(A_893,B_892,B_892,A_893,C_890,D_891),k6_partfun1(A_893))
      | k2_relset_1(A_893,B_892,C_890) != B_892
      | ~ m1_subset_1(D_891,k1_zfmisc_1(k2_zfmisc_1(B_892,A_893)))
      | ~ v1_funct_2(D_891,B_892,A_893)
      | ~ v1_funct_1(D_891)
      | ~ m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(A_893,B_892)))
      | ~ v1_funct_2(C_890,A_893,B_892)
      | ~ v1_funct_1(C_890) ) ),
    inference(cnfTransformation,[status(thm)],[f_417])).

tff(c_16316,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_5'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_7','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_152,c_16313])).

tff(c_16319,plain,
    ( k2_funct_1('#skF_6') = '#skF_7'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_162,c_160,c_158,c_154,c_15687,c_1379,c_16316])).

tff(c_16320,plain,(
    k2_funct_1('#skF_6') = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_15828,c_16319])).

tff(c_11180,plain,(
    ! [A_740,B_741] :
      ( k2_funct_2(A_740,B_741) = k2_funct_1(B_741)
      | ~ m1_subset_1(B_741,k1_zfmisc_1(k2_zfmisc_1(A_740,A_740)))
      | ~ v3_funct_2(B_741,A_740,A_740)
      | ~ v1_funct_2(B_741,A_740,A_740)
      | ~ v1_funct_1(B_741) ) ),
    inference(cnfTransformation,[status(thm)],[f_319])).

tff(c_11223,plain,
    ( k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_11180])).

tff(c_11243,plain,(
    k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_164,c_11223])).

tff(c_150,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_7',k2_funct_2('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_439])).

tff(c_11253,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_7',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11243,c_150])).

tff(c_16338,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16320,c_11253])).

tff(c_16357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_769,c_16338])).

tff(c_16358,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13121])).

tff(c_16420,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16358,c_282])).

tff(c_16431,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_16420])).

tff(c_16433,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_30,plain,(
    ! [A_28] : m1_subset_1('#skF_2'(A_28),k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_520,plain,(
    ! [B_203,A_204] :
      ( v1_xboole_0('#skF_2'(k2_zfmisc_1(B_203,A_204)))
      | ~ v1_xboole_0(A_204) ) ),
    inference(resolution,[status(thm)],[c_30,c_486])).

tff(c_28,plain,(
    ! [A_28] : ~ v1_subset_1('#skF_2'(A_28),A_28) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_16511,plain,(
    ! [B_908,A_909] :
      ( v1_subset_1(B_908,A_909)
      | ~ v1_xboole_0(B_908)
      | ~ m1_subset_1(B_908,k1_zfmisc_1(A_909))
      | v1_xboole_0(A_909) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16529,plain,(
    ! [A_28] :
      ( v1_subset_1('#skF_2'(A_28),A_28)
      | ~ v1_xboole_0('#skF_2'(A_28))
      | v1_xboole_0(A_28) ) ),
    inference(resolution,[status(thm)],[c_30,c_16511])).

tff(c_16556,plain,(
    ! [A_910] :
      ( ~ v1_xboole_0('#skF_2'(A_910))
      | v1_xboole_0(A_910) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_16529])).

tff(c_16566,plain,(
    ! [B_912,A_913] :
      ( v1_xboole_0(k2_zfmisc_1(B_912,A_913))
      | ~ v1_xboole_0(A_913) ) ),
    inference(resolution,[status(thm)],[c_520,c_16556])).

tff(c_274,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_154,c_249])).

tff(c_284,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_274])).

tff(c_16583,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_16566,c_284])).

tff(c_16591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16433,c_16583])).

tff(c_16593,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_274])).

tff(c_16690,plain,(
    ! [C_925,B_926,A_927] :
      ( ~ v1_xboole_0(C_925)
      | ~ m1_subset_1(B_926,k1_zfmisc_1(C_925))
      | ~ r2_hidden(A_927,B_926) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_16704,plain,(
    ! [A_927] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5'))
      | ~ r2_hidden(A_927,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_162,c_16690])).

tff(c_16717,plain,(
    ! [A_927] : ~ r2_hidden(A_927,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16593,c_16704])).

tff(c_137234,plain,(
    ! [C_5455,A_5456] :
      ( r1_tarski('#skF_6',C_5455)
      | ~ m1_subset_1(C_5455,k1_zfmisc_1(A_5456))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_5456)) ) ),
    inference(resolution,[status(thm)],[c_137154,c_16717])).

tff(c_137271,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_6',k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_137234])).

tff(c_137278,plain,(
    ! [A_10] : ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(splitLeft,[status(thm)],[c_137271])).

tff(c_137280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137278,c_162])).

tff(c_137281,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_137271])).

tff(c_206,plain,(
    ! [A_146,B_147] :
      ( r1_tarski(A_146,B_147)
      | ~ m1_subset_1(A_146,k1_zfmisc_1(B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_230,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(resolution,[status(thm)],[c_10,c_206])).

tff(c_138294,plain,(
    ! [C_5496,A_5497,B_5498] :
      ( r1_tarski(C_5496,k3_subset_1(A_5497,B_5498))
      | ~ r1_tarski(B_5498,k3_subset_1(A_5497,C_5496))
      | ~ m1_subset_1(C_5496,k1_zfmisc_1(A_5497))
      | ~ m1_subset_1(B_5498,k1_zfmisc_1(A_5497)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_138318,plain,(
    ! [C_5496,A_5497] :
      ( r1_tarski(C_5496,k3_subset_1(A_5497,k1_xboole_0))
      | ~ m1_subset_1(C_5496,k1_zfmisc_1(A_5497))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5497)) ) ),
    inference(resolution,[status(thm)],[c_230,c_138294])).

tff(c_138507,plain,(
    ! [C_5504,A_5505] :
      ( r1_tarski(C_5504,k3_subset_1(A_5505,k1_xboole_0))
      | ~ m1_subset_1(C_5504,k1_zfmisc_1(A_5505)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138318])).

tff(c_8,plain,(
    ! [B_8,A_7,C_9] :
      ( k1_xboole_0 = B_8
      | ~ r1_tarski(B_8,k3_subset_1(A_7,C_9))
      | ~ r1_tarski(B_8,C_9)
      | ~ m1_subset_1(C_9,k1_zfmisc_1(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_138520,plain,(
    ! [C_5504,A_5505] :
      ( k1_xboole_0 = C_5504
      | ~ r1_tarski(C_5504,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5505))
      | ~ m1_subset_1(C_5504,k1_zfmisc_1(A_5505)) ) ),
    inference(resolution,[status(thm)],[c_138507,c_8])).

tff(c_138591,plain,(
    ! [C_5510,A_5511] :
      ( k1_xboole_0 = C_5510
      | ~ r1_tarski(C_5510,k1_xboole_0)
      | ~ m1_subset_1(C_5510,k1_zfmisc_1(A_5511)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_138520])).

tff(c_138627,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_162,c_138591])).

tff(c_138645,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137281,c_138627])).

tff(c_16700,plain,(
    ! [A_927] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5'))
      | ~ r2_hidden(A_927,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_154,c_16690])).

tff(c_16713,plain,(
    ! [A_927] : ~ r2_hidden(A_927,'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16593,c_16700])).

tff(c_137316,plain,(
    ! [C_5462,A_5463] :
      ( r1_tarski('#skF_7',C_5462)
      | ~ m1_subset_1(C_5462,k1_zfmisc_1(A_5463))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_5463)) ) ),
    inference(resolution,[status(thm)],[c_137154,c_16713])).

tff(c_137353,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_7',k1_xboole_0)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_137316])).

tff(c_137360,plain,(
    ! [A_10] : ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ),
    inference(splitLeft,[status(thm)],[c_137353])).

tff(c_137362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_137360,c_154])).

tff(c_137363,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_137353])).

tff(c_138621,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_154,c_138591])).

tff(c_138641,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_137363,c_138621])).

tff(c_138719,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_138645,c_138641])).

tff(c_16902,plain,(
    ! [A_978,B_979,D_980] :
      ( r2_relset_1(A_978,B_979,D_980,D_980)
      | ~ m1_subset_1(D_980,k1_zfmisc_1(k2_zfmisc_1(A_978,B_979))) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_16929,plain,(
    ! [A_978,B_979] : r2_relset_1(A_978,B_979,k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_16902])).

tff(c_138697,plain,(
    ! [A_978,B_979] : r2_relset_1(A_978,B_979,'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138641,c_138641,c_16929])).

tff(c_141164,plain,(
    ! [A_978,B_979] : r2_relset_1(A_978,B_979,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138719,c_138697])).

tff(c_138704,plain,(
    ! [A_10] : m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138641,c_10])).

tff(c_140861,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138704])).

tff(c_27382,plain,(
    ! [A_1539,B_1540,C_1541] :
      ( k2_relset_1(A_1539,B_1540,C_1541) = k2_relat_1(C_1541)
      | ~ m1_subset_1(C_1541,k1_zfmisc_1(k2_zfmisc_1(A_1539,B_1540))) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_27427,plain,(
    ! [A_1539,B_1540] : k2_relset_1(A_1539,B_1540,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_27382])).

tff(c_138694,plain,(
    ! [A_1539,B_1540] : k2_relset_1(A_1539,B_1540,'#skF_7') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138641,c_138641,c_27427])).

tff(c_141343,plain,(
    ! [A_1539,B_1540] : k2_relset_1(A_1539,B_1540,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138719,c_138694])).

tff(c_140601,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6'),k6_partfun1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_152])).

tff(c_152923,plain,(
    ! [A_6106,B_6107,C_6108,D_6109] :
      ( k2_relset_1(A_6106,B_6107,C_6108) = B_6107
      | ~ r2_relset_1(B_6107,B_6107,k1_partfun1(B_6107,A_6106,A_6106,B_6107,D_6109,C_6108),k6_partfun1(B_6107))
      | ~ m1_subset_1(D_6109,k1_zfmisc_1(k2_zfmisc_1(B_6107,A_6106)))
      | ~ v1_funct_2(D_6109,B_6107,A_6106)
      | ~ v1_funct_1(D_6109)
      | ~ m1_subset_1(C_6108,k1_zfmisc_1(k2_zfmisc_1(A_6106,B_6107)))
      | ~ v1_funct_2(C_6108,A_6106,B_6107)
      | ~ v1_funct_1(C_6108) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_152926,plain,
    ( k2_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140601,c_152923])).

tff(c_152929,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_140861,c_141343,c_152926])).

tff(c_152930,plain,(
    ! [A_1539,B_1540] : k2_relset_1(A_1539,B_1540,'#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_152929,c_141343])).

tff(c_16925,plain,(
    ! [A_93] : r2_relset_1(A_93,A_93,k6_partfun1(A_93),k6_partfun1(A_93)) ),
    inference(resolution,[status(thm)],[c_122,c_16902])).

tff(c_28071,plain,(
    ! [C_1618,A_1619,B_1620] :
      ( v2_funct_1(C_1618)
      | ~ v3_funct_2(C_1618,A_1619,B_1620)
      | ~ v1_funct_1(C_1618)
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(A_1619,B_1620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_28102,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_28071])).

tff(c_28119,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_164,c_28102])).

tff(c_141937,plain,(
    ! [A_5659,B_5660,C_5661,D_5662] :
      ( k2_relset_1(A_5659,B_5660,C_5661) = B_5660
      | ~ r2_relset_1(B_5660,B_5660,k1_partfun1(B_5660,A_5659,A_5659,B_5660,D_5662,C_5661),k6_partfun1(B_5660))
      | ~ m1_subset_1(D_5662,k1_zfmisc_1(k2_zfmisc_1(B_5660,A_5659)))
      | ~ v1_funct_2(D_5662,B_5660,A_5659)
      | ~ v1_funct_1(D_5662)
      | ~ m1_subset_1(C_5661,k1_zfmisc_1(k2_zfmisc_1(A_5659,B_5660)))
      | ~ v1_funct_2(C_5661,A_5659,B_5660)
      | ~ v1_funct_1(C_5661) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_141940,plain,
    ( k2_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140601,c_141937])).

tff(c_141943,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_140861,c_141343,c_141940])).

tff(c_141944,plain,(
    ! [A_1539,B_1540] : k2_relset_1(A_1539,B_1540,'#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141943,c_141343])).

tff(c_148,plain,(
    ! [C_120,D_122,B_119,A_118] :
      ( k2_funct_1(C_120) = D_122
      | k1_xboole_0 = B_119
      | k1_xboole_0 = A_118
      | ~ v2_funct_1(C_120)
      | ~ r2_relset_1(A_118,A_118,k1_partfun1(A_118,B_119,B_119,A_118,C_120,D_122),k6_partfun1(A_118))
      | k2_relset_1(A_118,B_119,C_120) != B_119
      | ~ m1_subset_1(D_122,k1_zfmisc_1(k2_zfmisc_1(B_119,A_118)))
      | ~ v1_funct_2(D_122,B_119,A_118)
      | ~ v1_funct_1(D_122)
      | ~ m1_subset_1(C_120,k1_zfmisc_1(k2_zfmisc_1(A_118,B_119)))
      | ~ v1_funct_2(C_120,A_118,B_119)
      | ~ v1_funct_1(C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_417])).

tff(c_147504,plain,(
    ! [C_5891,D_5892,B_5893,A_5894] :
      ( k2_funct_1(C_5891) = D_5892
      | B_5893 = '#skF_6'
      | A_5894 = '#skF_6'
      | ~ v2_funct_1(C_5891)
      | ~ r2_relset_1(A_5894,A_5894,k1_partfun1(A_5894,B_5893,B_5893,A_5894,C_5891,D_5892),k6_partfun1(A_5894))
      | k2_relset_1(A_5894,B_5893,C_5891) != B_5893
      | ~ m1_subset_1(D_5892,k1_zfmisc_1(k2_zfmisc_1(B_5893,A_5894)))
      | ~ v1_funct_2(D_5892,B_5893,A_5894)
      | ~ v1_funct_1(D_5892)
      | ~ m1_subset_1(C_5891,k1_zfmisc_1(k2_zfmisc_1(A_5894,B_5893)))
      | ~ v1_funct_2(C_5891,A_5894,B_5893)
      | ~ v1_funct_1(C_5891) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138645,c_138645,c_148])).

tff(c_147507,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_140601,c_147504])).

tff(c_147510,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_140861,c_141944,c_28119,c_147507])).

tff(c_147511,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_147510])).

tff(c_138537,plain,(
    ! [D_5506,C_5507,A_5508,B_5509] :
      ( D_5506 = C_5507
      | ~ r2_relset_1(A_5508,B_5509,C_5507,D_5506)
      | ~ m1_subset_1(D_5506,k1_zfmisc_1(k2_zfmisc_1(A_5508,B_5509)))
      | ~ m1_subset_1(C_5507,k1_zfmisc_1(k2_zfmisc_1(A_5508,B_5509))) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_138555,plain,
    ( k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k6_partfun1('#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_152,c_138537])).

tff(c_138590,plain,
    ( k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_7'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_138555])).

tff(c_141846,plain,
    ( k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6') = k6_partfun1('#skF_5')
    | ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138719,c_138590])).

tff(c_141847,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(splitLeft,[status(thm)],[c_141846])).

tff(c_152727,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_6','#skF_6','#skF_6','#skF_6','#skF_6','#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_147511,c_147511,c_147511,c_147511,c_147511,c_147511,c_141847])).

tff(c_152730,plain,
    ( ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6')))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_108,c_152727])).

tff(c_152737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_140861,c_152730])).

tff(c_152738,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_147510])).

tff(c_140804,plain,(
    ! [A_5588,B_5589] :
      ( k2_funct_2(A_5588,B_5589) = k2_funct_1(B_5589)
      | ~ m1_subset_1(B_5589,k1_zfmisc_1(k2_zfmisc_1(A_5588,A_5588)))
      | ~ v3_funct_2(B_5589,A_5588,A_5588)
      | ~ v1_funct_2(B_5589,A_5588,A_5588)
      | ~ v1_funct_1(B_5589) ) ),
    inference(cnfTransformation,[status(thm)],[f_319])).

tff(c_140837,plain,
    ( k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_140804])).

tff(c_140848,plain,(
    k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_164,c_140837])).

tff(c_140602,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6',k2_funct_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_150])).

tff(c_141023,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140848,c_140602])).

tff(c_152829,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152738,c_141023])).

tff(c_152843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141164,c_152829])).

tff(c_152844,plain,(
    k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6') = k6_partfun1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_141846])).

tff(c_194083,plain,(
    ! [C_7080,D_7081,B_7082,A_7083] :
      ( k2_funct_1(C_7080) = D_7081
      | B_7082 = '#skF_6'
      | A_7083 = '#skF_6'
      | ~ v2_funct_1(C_7080)
      | ~ r2_relset_1(A_7083,A_7083,k1_partfun1(A_7083,B_7082,B_7082,A_7083,C_7080,D_7081),k6_partfun1(A_7083))
      | k2_relset_1(A_7083,B_7082,C_7080) != B_7082
      | ~ m1_subset_1(D_7081,k1_zfmisc_1(k2_zfmisc_1(B_7082,A_7083)))
      | ~ v1_funct_2(D_7081,B_7082,A_7083)
      | ~ v1_funct_1(D_7081)
      | ~ m1_subset_1(C_7080,k1_zfmisc_1(k2_zfmisc_1(A_7083,B_7082)))
      | ~ v1_funct_2(C_7080,A_7083,B_7082)
      | ~ v1_funct_1(C_7080) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138645,c_138645,c_148])).

tff(c_194086,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6'
    | '#skF_5' = '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | ~ r2_relset_1('#skF_5','#skF_5',k6_partfun1('#skF_5'),k6_partfun1('#skF_5'))
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_152844,c_194083])).

tff(c_194088,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_140861,c_168,c_166,c_140861,c_152930,c_16925,c_28119,c_194086])).

tff(c_194089,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_194088])).

tff(c_141175,plain,(
    ! [A_5603,B_5604] :
      ( m1_subset_1(k2_funct_2(A_5603,B_5604),k1_zfmisc_1(k2_zfmisc_1(A_5603,A_5603)))
      | ~ m1_subset_1(B_5604,k1_zfmisc_1(k2_zfmisc_1(A_5603,A_5603)))
      | ~ v3_funct_2(B_5604,A_5603,A_5603)
      | ~ v1_funct_2(B_5604,A_5603,A_5603)
      | ~ v1_funct_1(B_5604) ) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_141224,plain,
    ( m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_140848,c_141175])).

tff(c_141243,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_164,c_140861,c_141224])).

tff(c_194098,plain,(
    m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194089,c_194089,c_141243])).

tff(c_138700,plain,(
    ! [A_10] : r1_tarski('#skF_7',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138641,c_230])).

tff(c_140684,plain,(
    ! [A_10] : r1_tarski('#skF_6',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138700])).

tff(c_137250,plain,
    ( r1_tarski('#skF_6','#skF_7')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5'))) ),
    inference(resolution,[status(thm)],[c_154,c_137234])).

tff(c_137266,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_137250])).

tff(c_138042,plain,(
    ! [D_5490,B_5488,E_5487,C_5489,A_5486] :
      ( m1_subset_1(E_5487,k1_zfmisc_1(k2_zfmisc_1(B_5488,D_5490)))
      | ~ r1_tarski(C_5489,D_5490)
      | ~ r1_tarski(A_5486,B_5488)
      | ~ m1_subset_1(E_5487,k1_zfmisc_1(k2_zfmisc_1(A_5486,C_5489))) ) ),
    inference(cnfTransformation,[status(thm)],[f_217])).

tff(c_138113,plain,(
    ! [E_5487,B_5488,A_5486] :
      ( m1_subset_1(E_5487,k1_zfmisc_1(k2_zfmisc_1(B_5488,'#skF_7')))
      | ~ r1_tarski(A_5486,B_5488)
      | ~ m1_subset_1(E_5487,k1_zfmisc_1(k2_zfmisc_1(A_5486,'#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_137266,c_138042])).

tff(c_195031,plain,(
    ! [E_7115,B_7116,A_7117] :
      ( m1_subset_1(E_7115,k1_zfmisc_1(k2_zfmisc_1(B_7116,'#skF_6')))
      | ~ r1_tarski(A_7117,B_7116)
      | ~ m1_subset_1(E_7115,k1_zfmisc_1(k2_zfmisc_1(A_7117,'#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138719,c_138113])).

tff(c_219889,plain,(
    ! [E_7750,A_7751] :
      ( m1_subset_1(E_7750,k1_zfmisc_1(k2_zfmisc_1(A_7751,'#skF_6')))
      | ~ m1_subset_1(E_7750,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_140684,c_195031])).

tff(c_220519,plain,(
    ! [A_7758] : m1_subset_1(k2_funct_1('#skF_6'),k1_zfmisc_1(k2_zfmisc_1(A_7758,'#skF_6'))) ),
    inference(resolution,[status(thm)],[c_194098,c_219889])).

tff(c_32,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_220677,plain,(
    ! [A_7759] : r1_tarski(k2_funct_1('#skF_6'),k2_zfmisc_1(A_7759,'#skF_6')) ),
    inference(resolution,[status(thm)],[c_220519,c_32])).

tff(c_34,plain,(
    ! [A_30,B_31] :
      ( m1_subset_1(A_30,k1_zfmisc_1(B_31))
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_27900,plain,(
    ! [C_1609,A_1610] :
      ( k1_xboole_0 = C_1609
      | ~ v1_funct_2(C_1609,A_1610,k1_xboole_0)
      | k1_xboole_0 = A_1610
      | ~ m1_subset_1(C_1609,k1_zfmisc_1(k2_zfmisc_1(A_1610,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_266])).

tff(c_27938,plain,(
    ! [A_30,A_1610] :
      ( k1_xboole_0 = A_30
      | ~ v1_funct_2(A_30,A_1610,k1_xboole_0)
      | k1_xboole_0 = A_1610
      | ~ r1_tarski(A_30,k2_zfmisc_1(A_1610,k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_34,c_27900])).

tff(c_196611,plain,(
    ! [A_30,A_1610] :
      ( A_30 = '#skF_6'
      | ~ v1_funct_2(A_30,A_1610,'#skF_6')
      | A_1610 = '#skF_6'
      | ~ r1_tarski(A_30,k2_zfmisc_1(A_1610,'#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_138645,c_138645,c_138645,c_138645,c_27938])).

tff(c_220740,plain,(
    ! [A_7759] :
      ( k2_funct_1('#skF_6') = '#skF_6'
      | ~ v1_funct_2(k2_funct_1('#skF_6'),A_7759,'#skF_6')
      | A_7759 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_220677,c_196611])).

tff(c_227475,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_220740])).

tff(c_194103,plain,(
    ~ r2_relset_1('#skF_6','#skF_6','#skF_6',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194089,c_194089,c_141023])).

tff(c_227498,plain,(
    ~ r2_relset_1('#skF_6','#skF_6','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227475,c_194103])).

tff(c_227524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141164,c_227498])).

tff(c_227526,plain,(
    k2_funct_1('#skF_6') != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_220740])).

tff(c_19825,plain,(
    ! [A_1211,B_1212,C_1213] :
      ( r2_hidden('#skF_1'(A_1211,B_1212,C_1213),B_1212)
      | r1_tarski(B_1212,C_1213)
      | ~ m1_subset_1(C_1213,k1_zfmisc_1(A_1211))
      | ~ m1_subset_1(B_1212,k1_zfmisc_1(A_1211)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_19929,plain,(
    ! [C_1219,A_1220] :
      ( r1_tarski('#skF_6',C_1219)
      | ~ m1_subset_1(C_1219,k1_zfmisc_1(A_1220))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_1220)) ) ),
    inference(resolution,[status(thm)],[c_19825,c_16717])).

tff(c_19966,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_6',k1_xboole_0)
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_19929])).

tff(c_19973,plain,(
    ! [A_10] : ~ m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(splitLeft,[status(thm)],[c_19966])).

tff(c_19975,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_19973,c_162])).

tff(c_19976,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_19966])).

tff(c_20893,plain,(
    ! [C_1260,A_1261,B_1262] :
      ( r1_tarski(C_1260,k3_subset_1(A_1261,B_1262))
      | ~ r1_tarski(B_1262,k3_subset_1(A_1261,C_1260))
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(A_1261))
      | ~ m1_subset_1(B_1262,k1_zfmisc_1(A_1261)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_20914,plain,(
    ! [C_1260,A_1261] :
      ( r1_tarski(C_1260,k3_subset_1(A_1261,k1_xboole_0))
      | ~ m1_subset_1(C_1260,k1_zfmisc_1(A_1261))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1261)) ) ),
    inference(resolution,[status(thm)],[c_230,c_20893])).

tff(c_25098,plain,(
    ! [C_1407,A_1408] :
      ( r1_tarski(C_1407,k3_subset_1(A_1408,k1_xboole_0))
      | ~ m1_subset_1(C_1407,k1_zfmisc_1(A_1408)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20914])).

tff(c_25109,plain,(
    ! [C_1407,A_1408] :
      ( k1_xboole_0 = C_1407
      | ~ r1_tarski(C_1407,k1_xboole_0)
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1408))
      | ~ m1_subset_1(C_1407,k1_zfmisc_1(A_1408)) ) ),
    inference(resolution,[status(thm)],[c_25098,c_8])).

tff(c_25123,plain,(
    ! [C_1409,A_1410] :
      ( k1_xboole_0 = C_1409
      | ~ r1_tarski(C_1409,k1_xboole_0)
      | ~ m1_subset_1(C_1409,k1_zfmisc_1(A_1410)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_25109])).

tff(c_25159,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski('#skF_6',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_162,c_25123])).

tff(c_25177,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19976,c_25159])).

tff(c_20063,plain,(
    ! [C_1229,A_1230] :
      ( r1_tarski('#skF_7',C_1229)
      | ~ m1_subset_1(C_1229,k1_zfmisc_1(A_1230))
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_1230)) ) ),
    inference(resolution,[status(thm)],[c_19825,c_16713])).

tff(c_20100,plain,(
    ! [A_10] :
      ( r1_tarski('#skF_7',k1_xboole_0)
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ) ),
    inference(resolution,[status(thm)],[c_10,c_20063])).

tff(c_20107,plain,(
    ! [A_10] : ~ m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ),
    inference(splitLeft,[status(thm)],[c_20100])).

tff(c_20109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20107,c_154])).

tff(c_20110,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_20100])).

tff(c_25153,plain,
    ( k1_xboole_0 = '#skF_7'
    | ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_154,c_25123])).

tff(c_25173,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20110,c_25153])).

tff(c_25260,plain,(
    '#skF_7' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25177,c_25173])).

tff(c_25238,plain,(
    ! [A_978,B_979] : r2_relset_1(A_978,B_979,'#skF_7','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25173,c_25173,c_16929])).

tff(c_25892,plain,(
    ! [A_978,B_979] : r2_relset_1(A_978,B_979,'#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25260,c_25260,c_25238])).

tff(c_276,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_5')) ),
    inference(resolution,[status(thm)],[c_162,c_249])).

tff(c_16595,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16593,c_276])).

tff(c_25245,plain,(
    ! [A_10] : m1_subset_1('#skF_7',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25173,c_10])).

tff(c_25575,plain,(
    ! [A_10] : m1_subset_1('#skF_6',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25260,c_25245])).

tff(c_17144,plain,(
    ! [A_1003,B_1004,C_1005] :
      ( k2_relset_1(A_1003,B_1004,C_1005) = k2_relat_1(C_1005)
      | ~ m1_subset_1(C_1005,k1_zfmisc_1(k2_zfmisc_1(A_1003,B_1004))) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_17189,plain,(
    ! [A_1003,B_1004] : k2_relset_1(A_1003,B_1004,k1_xboole_0) = k2_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_17144])).

tff(c_25235,plain,(
    ! [A_1003,B_1004] : k2_relset_1(A_1003,B_1004,'#skF_7') = k2_relat_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25173,c_25173,c_17189])).

tff(c_26015,plain,(
    ! [A_1003,B_1004] : k2_relset_1(A_1003,B_1004,'#skF_6') = k2_relat_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_25260,c_25260,c_25235])).

tff(c_25335,plain,(
    r2_relset_1('#skF_5','#skF_5',k1_partfun1('#skF_5','#skF_5','#skF_5','#skF_5','#skF_6','#skF_6'),k6_partfun1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25260,c_152])).

tff(c_26664,plain,(
    ! [A_1478,B_1479,C_1480,D_1481] :
      ( k2_relset_1(A_1478,B_1479,C_1480) = B_1479
      | ~ r2_relset_1(B_1479,B_1479,k1_partfun1(B_1479,A_1478,A_1478,B_1479,D_1481,C_1480),k6_partfun1(B_1479))
      | ~ m1_subset_1(D_1481,k1_zfmisc_1(k2_zfmisc_1(B_1479,A_1478)))
      | ~ v1_funct_2(D_1481,B_1479,A_1478)
      | ~ v1_funct_1(D_1481)
      | ~ m1_subset_1(C_1480,k1_zfmisc_1(k2_zfmisc_1(A_1478,B_1479)))
      | ~ v1_funct_2(C_1480,A_1478,B_1479)
      | ~ v1_funct_1(C_1480) ) ),
    inference(cnfTransformation,[status(thm)],[f_336])).

tff(c_26667,plain,
    ( k2_relset_1('#skF_5','#skF_5','#skF_6') = '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_25335,c_26664])).

tff(c_26670,plain,(
    k2_relat_1('#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_25575,c_26015,c_26667])).

tff(c_26671,plain,(
    ! [A_1003,B_1004] : k2_relset_1(A_1003,B_1004,'#skF_6') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26670,c_26015])).

tff(c_17860,plain,(
    ! [C_1080,A_1081,B_1082] :
      ( v2_funct_1(C_1080)
      | ~ v3_funct_2(C_1080,A_1081,B_1082)
      | ~ v1_funct_1(C_1080)
      | ~ m1_subset_1(C_1080,k1_zfmisc_1(k2_zfmisc_1(A_1081,B_1082))) ) ),
    inference(cnfTransformation,[status(thm)],[f_248])).

tff(c_17895,plain,
    ( v2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_17860])).

tff(c_17913,plain,(
    v2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_164,c_17895])).

tff(c_27118,plain,(
    ! [C_1518,D_1519,B_1520,A_1521] :
      ( k2_funct_1(C_1518) = D_1519
      | B_1520 = '#skF_6'
      | A_1521 = '#skF_6'
      | ~ v2_funct_1(C_1518)
      | ~ r2_relset_1(A_1521,A_1521,k1_partfun1(A_1521,B_1520,B_1520,A_1521,C_1518,D_1519),k6_partfun1(A_1521))
      | k2_relset_1(A_1521,B_1520,C_1518) != B_1520
      | ~ m1_subset_1(D_1519,k1_zfmisc_1(k2_zfmisc_1(B_1520,A_1521)))
      | ~ v1_funct_2(D_1519,B_1520,A_1521)
      | ~ v1_funct_1(D_1519)
      | ~ m1_subset_1(C_1518,k1_zfmisc_1(k2_zfmisc_1(A_1521,B_1520)))
      | ~ v1_funct_2(C_1518,A_1521,B_1520)
      | ~ v1_funct_1(C_1518) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25177,c_25177,c_148])).

tff(c_27121,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6'
    | ~ v2_funct_1('#skF_6')
    | k2_relset_1('#skF_5','#skF_5','#skF_6') != '#skF_5'
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_5','#skF_5')))
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_25335,c_27118])).

tff(c_27124,plain,
    ( k2_funct_1('#skF_6') = '#skF_6'
    | '#skF_5' = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_25575,c_26671,c_17913,c_27121])).

tff(c_27125,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_27124])).

tff(c_16930,plain,(
    ! [C_981,A_982,B_983] :
      ( v1_partfun1(C_981,A_982)
      | ~ m1_subset_1(C_981,k1_zfmisc_1(k2_zfmisc_1(A_982,B_983)))
      | ~ v1_xboole_0(A_982) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_16963,plain,
    ( v1_partfun1('#skF_7','#skF_5')
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_154,c_16930])).

tff(c_16968,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_16963])).

tff(c_27145,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27125,c_16968])).

tff(c_27156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16595,c_27145])).

tff(c_27157,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_27124])).

tff(c_25265,plain,(
    ! [A_1411,B_1412] :
      ( k2_funct_2(A_1411,B_1412) = k2_funct_1(B_1412)
      | ~ m1_subset_1(B_1412,k1_zfmisc_1(k2_zfmisc_1(A_1411,A_1411)))
      | ~ v3_funct_2(B_1412,A_1411,A_1411)
      | ~ v1_funct_2(B_1412,A_1411,A_1411)
      | ~ v1_funct_1(B_1412) ) ),
    inference(cnfTransformation,[status(thm)],[f_319])).

tff(c_25301,plain,
    ( k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6')
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_25265])).

tff(c_25315,plain,(
    k2_funct_2('#skF_5','#skF_6') = k2_funct_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_164,c_25301])).

tff(c_25336,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6',k2_funct_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25260,c_150])).

tff(c_25721,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6',k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25315,c_25336])).

tff(c_27209,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_27157,c_25721])).

tff(c_27223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_25892,c_27209])).

tff(c_27225,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_16963])).

tff(c_72,plain,(
    ! [C_58,B_56,A_55] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(B_56,A_55)))
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_197])).

tff(c_141717,plain,
    ( v1_xboole_0(k2_funct_1('#skF_6'))
    | ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_141243,c_72])).

tff(c_141770,plain,(
    v1_xboole_0(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27225,c_141717])).

tff(c_137301,plain,(
    ! [A_5461] :
      ( r1_tarski('#skF_6',k6_partfun1(A_5461))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(A_5461,A_5461))) ) ),
    inference(resolution,[status(thm)],[c_122,c_137234])).

tff(c_137309,plain,(
    r1_tarski('#skF_6',k6_partfun1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_162,c_137301])).

tff(c_141404,plain,(
    ! [E_5621,B_5622,A_5623] :
      ( m1_subset_1(E_5621,k1_zfmisc_1(k2_zfmisc_1(B_5622,k6_partfun1('#skF_5'))))
      | ~ r1_tarski(A_5623,B_5622)
      | ~ m1_subset_1(E_5621,k1_zfmisc_1(k2_zfmisc_1(A_5623,'#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_137309,c_138042])).

tff(c_141425,plain,(
    ! [E_5621,A_10] :
      ( m1_subset_1(E_5621,k1_zfmisc_1(k2_zfmisc_1(A_10,k6_partfun1('#skF_5'))))
      | ~ m1_subset_1(E_5621,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_140684,c_141404])).

tff(c_194339,plain,(
    ! [E_7092,A_7093] :
      ( m1_subset_1(E_7092,k1_zfmisc_1(k2_zfmisc_1(A_7093,k6_partfun1('#skF_6'))))
      | ~ m1_subset_1(E_7092,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194089,c_141425])).

tff(c_88,plain,(
    ! [C_78,A_75,B_76] :
      ( v1_partfun1(C_78,A_75)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76)))
      | ~ v1_xboole_0(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_206445,plain,(
    ! [E_7436,A_7437] :
      ( v1_partfun1(E_7436,A_7437)
      | ~ v1_xboole_0(A_7437)
      | ~ m1_subset_1(E_7436,k1_zfmisc_1(k2_zfmisc_1('#skF_6','#skF_6'))) ) ),
    inference(resolution,[status(thm)],[c_194339,c_88])).

tff(c_206487,plain,(
    ! [A_7437] :
      ( v1_partfun1(k2_funct_1('#skF_6'),A_7437)
      | ~ v1_xboole_0(A_7437) ) ),
    inference(resolution,[status(thm)],[c_194098,c_206445])).

tff(c_140628,plain,(
    ! [A_5583,B_5584] :
      ( v1_funct_1(k2_funct_2(A_5583,B_5584))
      | ~ m1_subset_1(B_5584,k1_zfmisc_1(k2_zfmisc_1(A_5583,A_5583)))
      | ~ v3_funct_2(B_5584,A_5583,A_5583)
      | ~ v1_funct_2(B_5584,A_5583,A_5583)
      | ~ v1_funct_1(B_5584) ) ),
    inference(cnfTransformation,[status(thm)],[f_294])).

tff(c_140661,plain,
    ( v1_funct_1(k2_funct_2('#skF_5','#skF_6'))
    | ~ v3_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_2('#skF_6','#skF_5','#skF_5')
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_162,c_140628])).

tff(c_140672,plain,(
    v1_funct_1(k2_funct_2('#skF_5','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_166,c_164,c_140661])).

tff(c_141022,plain,(
    v1_funct_1(k2_funct_1('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_140848,c_140672])).

tff(c_84,plain,(
    ! [C_74,A_72,B_73] :
      ( v1_funct_2(C_74,A_72,B_73)
      | ~ v1_partfun1(C_74,A_72)
      | ~ v1_funct_1(C_74)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(k2_zfmisc_1(A_72,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_229])).

tff(c_220576,plain,(
    ! [A_7758] :
      ( v1_funct_2(k2_funct_1('#skF_6'),A_7758,'#skF_6')
      | ~ v1_partfun1(k2_funct_1('#skF_6'),A_7758)
      | ~ v1_funct_1(k2_funct_1('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_220519,c_84])).

tff(c_220650,plain,(
    ! [A_7758] :
      ( v1_funct_2(k2_funct_1('#skF_6'),A_7758,'#skF_6')
      | ~ v1_partfun1(k2_funct_1('#skF_6'),A_7758) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141022,c_220576])).

tff(c_227579,plain,(
    ! [A_7891] :
      ( ~ v1_funct_2(k2_funct_1('#skF_6'),A_7891,'#skF_6')
      | A_7891 = '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_220740])).

tff(c_227589,plain,(
    ! [A_7892] :
      ( A_7892 = '#skF_6'
      | ~ v1_partfun1(k2_funct_1('#skF_6'),A_7892) ) ),
    inference(resolution,[status(thm)],[c_220650,c_227579])).

tff(c_227599,plain,(
    ! [A_7893] :
      ( A_7893 = '#skF_6'
      | ~ v1_xboole_0(A_7893) ) ),
    inference(resolution,[status(thm)],[c_206487,c_227589])).

tff(c_227644,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_141770,c_227599])).

tff(c_227692,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_227526,c_227644])).

tff(c_227693,plain,(
    k2_funct_1('#skF_6') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_194088])).

tff(c_227784,plain,(
    ~ r2_relset_1('#skF_5','#skF_5','#skF_6','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_227693,c_141023])).

tff(c_227798,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141164,c_227784])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 48.81/36.81  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.97/36.87  
% 48.97/36.87  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 48.97/36.87  %$ r2_relset_1 > v3_funct_2 > v1_funct_2 > v5_relat_1 > v5_funct_1 > v4_relat_1 > v2_funct_2 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v5_ordinal1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k8_setfam_1 > k6_setfam_1 > k5_relat_1 > k3_subset_1 > k2_zfmisc_1 > k2_funct_2 > k1_funct_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > np__1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 48.97/36.87  
% 48.97/36.87  %Foreground sorts:
% 48.97/36.87  
% 48.97/36.87  
% 48.97/36.87  %Background operators:
% 48.97/36.87  
% 48.97/36.87  
% 48.97/36.87  %Foreground operators:
% 48.97/36.87  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 48.97/36.87  tff(np__1, type, np__1: $i).
% 48.97/36.87  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 48.97/36.87  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 48.97/36.87  tff('#skF_2', type, '#skF_2': $i > $i).
% 48.97/36.87  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 48.97/36.87  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 48.97/36.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 48.97/36.87  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 48.97/36.87  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 48.97/36.87  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 48.97/36.87  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 48.97/36.87  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 48.97/36.87  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 48.97/36.87  tff('#skF_7', type, '#skF_7': $i).
% 48.97/36.87  tff(k2_funct_2, type, k2_funct_2: ($i * $i) > $i).
% 48.97/36.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 48.97/36.87  tff(v5_funct_1, type, v5_funct_1: ($i * $i) > $o).
% 48.97/36.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 48.97/36.87  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 48.97/36.87  tff(v5_ordinal1, type, v5_ordinal1: $i > $o).
% 48.97/36.87  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 48.97/36.87  tff('#skF_5', type, '#skF_5': $i).
% 48.97/36.87  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 48.97/36.87  tff('#skF_6', type, '#skF_6': $i).
% 48.97/36.87  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 48.97/36.87  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 48.97/36.87  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 48.97/36.87  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 48.97/36.87  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 48.97/36.87  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 48.97/36.87  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 48.97/36.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 48.97/36.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 48.97/36.87  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 48.97/36.87  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 48.97/36.87  tff('#skF_3', type, '#skF_3': $i > $i).
% 48.97/36.87  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 48.97/36.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 48.97/36.87  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 48.97/36.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 48.97/36.87  tff(v3_funct_2, type, v3_funct_2: ($i * $i * $i) > $o).
% 48.97/36.87  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 48.97/36.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 48.97/36.87  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 48.97/36.87  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 48.97/36.87  
% 49.26/36.91  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 49.26/36.91  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((![D]: (m1_subset_1(D, A) => (r2_hidden(D, B) => r2_hidden(D, C)))) => r1_tarski(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_subset_1)).
% 49.26/36.91  tff(f_439, negated_conjecture, ~(![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: ((((v1_funct_1(C) & v1_funct_2(C, A, A)) & v3_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (r2_relset_1(A, A, k1_partfun1(A, A, A, A, B, C), k6_partfun1(A)) => r2_relset_1(A, A, C, k2_funct_2(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_funct_2)).
% 49.26/36.91  tff(f_197, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 49.26/36.91  tff(f_209, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 49.26/36.91  tff(f_201, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 49.26/36.91  tff(f_248, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v3_funct_2(C, A, B)) => ((v1_funct_1(C) & v2_funct_1(C)) & v2_funct_2(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_funct_2)).
% 49.26/36.91  tff(f_392, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 49.26/36.91  tff(f_336, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 49.26/36.91  tff(f_71, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 49.26/36.91  tff(f_309, axiom, (![A, B]: (?[C]: ((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_xboole_0(C)) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_relset_1)).
% 49.26/36.91  tff(f_190, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 49.26/36.91  tff(f_160, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)) & (k2_relat_1(k5_relat_1(k2_funct_1(A), A)) = k2_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_funct_1)).
% 49.26/36.91  tff(f_298, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 49.26/36.91  tff(f_278, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 49.26/36.91  tff(f_357, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 49.26/36.91  tff(f_417, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 49.26/36.91  tff(f_319, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k2_funct_2(A, B) = k2_funct_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_funct_2)).
% 49.26/36.91  tff(f_102, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 49.26/36.91  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (v1_xboole_0(B) => v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_subset_1)).
% 49.26/36.91  tff(f_119, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 49.26/36.91  tff(f_106, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 49.26/36.91  tff(f_34, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_subset_1)).
% 49.26/36.91  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_subset_1)).
% 49.26/36.91  tff(f_294, axiom, (![A, B]: ((((v1_funct_1(B) & v1_funct_2(B, A, A)) & v3_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (((v1_funct_1(k2_funct_2(A, B)) & v1_funct_2(k2_funct_2(A, B), A, A)) & v3_funct_2(k2_funct_2(A, B), A, A)) & m1_subset_1(k2_funct_2(A, B), k1_zfmisc_1(k2_zfmisc_1(A, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_2)).
% 49.26/36.91  tff(f_217, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, C))) => ((r1_tarski(A, B) & r1_tarski(C, D)) => m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_relset_1)).
% 49.26/36.91  tff(f_266, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 49.26/36.91  tff(f_236, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_partfun1)).
% 49.26/36.91  tff(f_229, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_funct_2)).
% 49.26/36.91  tff(c_10, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 49.26/36.91  tff(c_137154, plain, (![A_5452, B_5453, C_5454]: (r2_hidden('#skF_1'(A_5452, B_5453, C_5454), B_5453) | r1_tarski(B_5453, C_5454) | ~m1_subset_1(C_5454, k1_zfmisc_1(A_5452)) | ~m1_subset_1(B_5453, k1_zfmisc_1(A_5452)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 49.26/36.91  tff(c_154, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_486, plain, (![C_202, B_203, A_204]: (v1_xboole_0(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(B_203, A_204))) | ~v1_xboole_0(A_204))), inference(cnfTransformation, [status(thm)], [f_197])).
% 49.26/36.91  tff(c_519, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_154, c_486])).
% 49.26/36.91  tff(c_524, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_519])).
% 49.26/36.91  tff(c_737, plain, (![A_240, B_241, D_242]: (r2_relset_1(A_240, B_241, D_242, D_242) | ~m1_subset_1(D_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 49.26/36.91  tff(c_769, plain, (r2_relset_1('#skF_5', '#skF_5', '#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_154, c_737])).
% 49.26/36.91  tff(c_160, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_158, plain, (v1_funct_2('#skF_7', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_823, plain, (![A_255, B_256, C_257]: (k2_relset_1(A_255, B_256, C_257)=k2_relat_1(C_257) | ~m1_subset_1(C_257, k1_zfmisc_1(k2_zfmisc_1(A_255, B_256))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 49.26/36.91  tff(c_865, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_7')=k2_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_823])).
% 49.26/36.91  tff(c_156, plain, (v3_funct_2('#skF_7', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_1331, plain, (![C_314, A_315, B_316]: (v2_funct_1(C_314) | ~v3_funct_2(C_314, A_315, B_316) | ~v1_funct_1(C_314) | ~m1_subset_1(C_314, k1_zfmisc_1(k2_zfmisc_1(A_315, B_316))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 49.26/36.91  tff(c_1355, plain, (v2_funct_1('#skF_7') | ~v3_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_1331])).
% 49.26/36.91  tff(c_1375, plain, (v2_funct_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_156, c_1355])).
% 49.26/36.91  tff(c_12515, plain, (![B_774, C_775, A_776]: (k6_partfun1(B_774)=k5_relat_1(k2_funct_1(C_775), C_775) | k1_xboole_0=B_774 | ~v2_funct_1(C_775) | k2_relset_1(A_776, B_774, C_775)!=B_774 | ~m1_subset_1(C_775, k1_zfmisc_1(k2_zfmisc_1(A_776, B_774))) | ~v1_funct_2(C_775, A_776, B_774) | ~v1_funct_1(C_775))), inference(cnfTransformation, [status(thm)], [f_392])).
% 49.26/36.91  tff(c_12550, plain, (k5_relat_1(k2_funct_1('#skF_7'), '#skF_7')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_7') | k2_relset_1('#skF_5', '#skF_5', '#skF_7')!='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_12515])).
% 49.26/36.91  tff(c_12583, plain, (k5_relat_1(k2_funct_1('#skF_7'), '#skF_7')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | k2_relat_1('#skF_7')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_158, c_865, c_1375, c_12550])).
% 49.26/36.91  tff(c_12726, plain, (k2_relat_1('#skF_7')!='#skF_5'), inference(splitLeft, [status(thm)], [c_12583])).
% 49.26/36.91  tff(c_168, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_166, plain, (v1_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_162, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_152, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k6_partfun1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_13112, plain, (![A_793, B_794, C_795, D_796]: (k2_relset_1(A_793, B_794, C_795)=B_794 | ~r2_relset_1(B_794, B_794, k1_partfun1(B_794, A_793, A_793, B_794, D_796, C_795), k6_partfun1(B_794)) | ~m1_subset_1(D_796, k1_zfmisc_1(k2_zfmisc_1(B_794, A_793))) | ~v1_funct_2(D_796, B_794, A_793) | ~v1_funct_1(D_796) | ~m1_subset_1(C_795, k1_zfmisc_1(k2_zfmisc_1(A_793, B_794))) | ~v1_funct_2(C_795, A_793, B_794) | ~v1_funct_1(C_795))), inference(cnfTransformation, [status(thm)], [f_336])).
% 49.26/36.91  tff(c_13115, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_7')='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_152, c_13112])).
% 49.26/36.91  tff(c_13118, plain, (k2_relat_1('#skF_7')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_158, c_154, c_168, c_166, c_162, c_865, c_13115])).
% 49.26/36.91  tff(c_13120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12726, c_13118])).
% 49.26/36.91  tff(c_13122, plain, (k2_relat_1('#skF_7')='#skF_5'), inference(splitRight, [status(thm)], [c_12583])).
% 49.26/36.91  tff(c_12389, plain, (![A_771, C_772, B_773]: (k6_partfun1(A_771)=k5_relat_1(C_772, k2_funct_1(C_772)) | k1_xboole_0=B_773 | ~v2_funct_1(C_772) | k2_relset_1(A_771, B_773, C_772)!=B_773 | ~m1_subset_1(C_772, k1_zfmisc_1(k2_zfmisc_1(A_771, B_773))) | ~v1_funct_2(C_772, A_771, B_773) | ~v1_funct_1(C_772))), inference(cnfTransformation, [status(thm)], [f_392])).
% 49.26/36.91  tff(c_12424, plain, (k5_relat_1('#skF_7', k2_funct_1('#skF_7'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_7') | k2_relset_1('#skF_5', '#skF_5', '#skF_7')!='#skF_5' | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_12389])).
% 49.26/36.91  tff(c_12457, plain, (k5_relat_1('#skF_7', k2_funct_1('#skF_7'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | k2_relat_1('#skF_7')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_160, c_158, c_865, c_1375, c_12424])).
% 49.26/36.91  tff(c_14724, plain, (k5_relat_1('#skF_7', k2_funct_1('#skF_7'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_13122, c_12457])).
% 49.26/36.91  tff(c_14725, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_14724])).
% 49.26/36.91  tff(c_249, plain, (![B_155, A_156]: (v1_xboole_0(B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)) | ~v1_xboole_0(A_156))), inference(cnfTransformation, [status(thm)], [f_71])).
% 49.26/36.91  tff(c_277, plain, (![A_10]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_10))), inference(resolution, [status(thm)], [c_10, c_249])).
% 49.26/36.91  tff(c_278, plain, (![A_10]: (~v1_xboole_0(A_10))), inference(splitLeft, [status(thm)], [c_277])).
% 49.26/36.91  tff(c_130, plain, (![A_94, B_95]: (v1_xboole_0('#skF_4'(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_309])).
% 49.26/36.91  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_278, c_130])).
% 49.26/36.91  tff(c_282, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_277])).
% 49.26/36.91  tff(c_14787, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14725, c_282])).
% 49.26/36.91  tff(c_14800, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_14787])).
% 49.26/36.91  tff(c_14802, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_14724])).
% 49.26/36.91  tff(c_867, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')=k2_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_823])).
% 49.26/36.91  tff(c_164, plain, (v3_funct_2('#skF_6', '#skF_5', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_1362, plain, (v2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_1331])).
% 49.26/36.91  tff(c_1379, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_164, c_1362])).
% 49.26/36.91  tff(c_12555, plain, (k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_12515])).
% 49.26/36.91  tff(c_12587, plain, (k5_relat_1(k2_funct_1('#skF_6'), '#skF_6')=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_867, c_1379, c_12555])).
% 49.26/36.91  tff(c_13133, plain, (k2_relat_1('#skF_6')!='#skF_5'), inference(splitLeft, [status(thm)], [c_12587])).
% 49.26/36.91  tff(c_321, plain, (![C_162, A_163, B_164]: (v1_relat_1(C_162) | ~m1_subset_1(C_162, k1_zfmisc_1(k2_zfmisc_1(A_163, B_164))))), inference(cnfTransformation, [status(thm)], [f_190])).
% 49.26/36.91  tff(c_354, plain, (v1_relat_1('#skF_7')), inference(resolution, [status(thm)], [c_154, c_321])).
% 49.26/36.91  tff(c_13121, plain, (k1_xboole_0='#skF_5' | k5_relat_1(k2_funct_1('#skF_7'), '#skF_7')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_12583])).
% 49.26/36.91  tff(c_13132, plain, (k5_relat_1(k2_funct_1('#skF_7'), '#skF_7')=k6_partfun1('#skF_5')), inference(splitLeft, [status(thm)], [c_13121])).
% 49.26/36.91  tff(c_52, plain, (![A_48]: (k2_relat_1(k5_relat_1(k2_funct_1(A_48), A_48))=k2_relat_1(A_48) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(cnfTransformation, [status(thm)], [f_160])).
% 49.26/36.91  tff(c_13143, plain, (k2_relat_1(k6_partfun1('#skF_5'))=k2_relat_1('#skF_7') | ~v2_funct_1('#skF_7') | ~v1_funct_1('#skF_7') | ~v1_relat_1('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_13132, c_52])).
% 49.26/36.91  tff(c_13154, plain, (k2_relat_1(k6_partfun1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_354, c_160, c_1375, c_13122, c_13143])).
% 49.26/36.91  tff(c_122, plain, (![A_93]: (m1_subset_1(k6_partfun1(A_93), k1_zfmisc_1(k2_zfmisc_1(A_93, A_93))))), inference(cnfTransformation, [status(thm)], [f_298])).
% 49.26/36.91  tff(c_864, plain, (![A_93]: (k2_relset_1(A_93, A_93, k6_partfun1(A_93))=k2_relat_1(k6_partfun1(A_93)))), inference(resolution, [status(thm)], [c_122, c_823])).
% 49.26/36.91  tff(c_108, plain, (![A_85, D_88, F_90, C_87, E_89, B_86]: (m1_subset_1(k1_partfun1(A_85, B_86, C_87, D_88, E_89, F_90), k1_zfmisc_1(k2_zfmisc_1(A_85, D_88))) | ~m1_subset_1(F_90, k1_zfmisc_1(k2_zfmisc_1(C_87, D_88))) | ~v1_funct_1(F_90) | ~m1_subset_1(E_89, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))) | ~v1_funct_1(E_89))), inference(cnfTransformation, [status(thm)], [f_278])).
% 49.26/36.91  tff(c_10742, plain, (![D_724, C_725, A_726, B_727]: (D_724=C_725 | ~r2_relset_1(A_726, B_727, C_725, D_724) | ~m1_subset_1(D_724, k1_zfmisc_1(k2_zfmisc_1(A_726, B_727))) | ~m1_subset_1(C_725, k1_zfmisc_1(k2_zfmisc_1(A_726, B_727))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 49.26/36.91  tff(c_10760, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_152, c_10742])).
% 49.26/36.91  tff(c_10795, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_10760])).
% 49.26/36.91  tff(c_15189, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_10795])).
% 49.26/36.91  tff(c_15629, plain, (~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_108, c_15189])).
% 49.26/36.91  tff(c_15636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_162, c_160, c_154, c_15629])).
% 49.26/36.91  tff(c_15637, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_10795])).
% 49.26/36.91  tff(c_138, plain, (![D_107, A_104, C_106, B_105, E_109]: (k2_relset_1(A_104, B_105, D_107)=B_105 | k1_xboole_0=C_106 | ~v2_funct_1(E_109) | k2_relset_1(A_104, C_106, k1_partfun1(A_104, B_105, B_105, C_106, D_107, E_109))!=C_106 | ~m1_subset_1(E_109, k1_zfmisc_1(k2_zfmisc_1(B_105, C_106))) | ~v1_funct_2(E_109, B_105, C_106) | ~v1_funct_1(E_109) | ~m1_subset_1(D_107, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))) | ~v1_funct_2(D_107, A_104, B_105) | ~v1_funct_1(D_107))), inference(cnfTransformation, [status(thm)], [f_357])).
% 49.26/36.91  tff(c_15663, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_7') | k2_relset_1('#skF_5', '#skF_5', k6_partfun1('#skF_5'))!='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_15637, c_138])).
% 49.26/36.91  tff(c_15682, plain, (k2_relat_1('#skF_6')='#skF_5' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_162, c_160, c_158, c_154, c_13154, c_864, c_1375, c_867, c_15663])).
% 49.26/36.91  tff(c_15684, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14802, c_13133, c_15682])).
% 49.26/36.91  tff(c_15686, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_12587])).
% 49.26/36.91  tff(c_12429, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_12389])).
% 49.26/36.91  tff(c_12461, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5' | k2_relat_1('#skF_6')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_867, c_1379, c_12429])).
% 49.26/36.91  tff(c_15753, plain, (k5_relat_1('#skF_6', k2_funct_1('#skF_6'))=k6_partfun1('#skF_5') | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15686, c_12461])).
% 49.26/36.91  tff(c_15754, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_15753])).
% 49.26/36.91  tff(c_15815, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_15754, c_282])).
% 49.26/36.91  tff(c_15826, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_15815])).
% 49.26/36.91  tff(c_15828, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_15753])).
% 49.26/36.91  tff(c_15687, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_15686, c_867])).
% 49.26/36.91  tff(c_16313, plain, (![C_890, D_891, B_892, A_893]: (k2_funct_1(C_890)=D_891 | k1_xboole_0=B_892 | k1_xboole_0=A_893 | ~v2_funct_1(C_890) | ~r2_relset_1(A_893, A_893, k1_partfun1(A_893, B_892, B_892, A_893, C_890, D_891), k6_partfun1(A_893)) | k2_relset_1(A_893, B_892, C_890)!=B_892 | ~m1_subset_1(D_891, k1_zfmisc_1(k2_zfmisc_1(B_892, A_893))) | ~v1_funct_2(D_891, B_892, A_893) | ~v1_funct_1(D_891) | ~m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(A_893, B_892))) | ~v1_funct_2(C_890, A_893, B_892) | ~v1_funct_1(C_890))), inference(cnfTransformation, [status(thm)], [f_417])).
% 49.26/36.91  tff(c_16316, plain, (k2_funct_1('#skF_6')='#skF_7' | k1_xboole_0='#skF_5' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_7', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_152, c_16313])).
% 49.26/36.91  tff(c_16319, plain, (k2_funct_1('#skF_6')='#skF_7' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_162, c_160, c_158, c_154, c_15687, c_1379, c_16316])).
% 49.26/36.91  tff(c_16320, plain, (k2_funct_1('#skF_6')='#skF_7'), inference(negUnitSimplification, [status(thm)], [c_15828, c_16319])).
% 49.26/36.91  tff(c_11180, plain, (![A_740, B_741]: (k2_funct_2(A_740, B_741)=k2_funct_1(B_741) | ~m1_subset_1(B_741, k1_zfmisc_1(k2_zfmisc_1(A_740, A_740))) | ~v3_funct_2(B_741, A_740, A_740) | ~v1_funct_2(B_741, A_740, A_740) | ~v1_funct_1(B_741))), inference(cnfTransformation, [status(thm)], [f_319])).
% 49.26/36.91  tff(c_11223, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_11180])).
% 49.26/36.91  tff(c_11243, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_164, c_11223])).
% 49.26/36.91  tff(c_150, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_7', k2_funct_2('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_439])).
% 49.26/36.91  tff(c_11253, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_7', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_11243, c_150])).
% 49.26/36.91  tff(c_16338, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_7', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16320, c_11253])).
% 49.26/36.91  tff(c_16357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_769, c_16338])).
% 49.26/36.91  tff(c_16358, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13121])).
% 49.26/36.91  tff(c_16420, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16358, c_282])).
% 49.26/36.91  tff(c_16431, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_16420])).
% 49.26/36.91  tff(c_16433, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_519])).
% 49.26/36.91  tff(c_30, plain, (![A_28]: (m1_subset_1('#skF_2'(A_28), k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_102])).
% 49.26/36.91  tff(c_520, plain, (![B_203, A_204]: (v1_xboole_0('#skF_2'(k2_zfmisc_1(B_203, A_204))) | ~v1_xboole_0(A_204))), inference(resolution, [status(thm)], [c_30, c_486])).
% 49.26/36.91  tff(c_28, plain, (![A_28]: (~v1_subset_1('#skF_2'(A_28), A_28))), inference(cnfTransformation, [status(thm)], [f_102])).
% 49.26/36.91  tff(c_16511, plain, (![B_908, A_909]: (v1_subset_1(B_908, A_909) | ~v1_xboole_0(B_908) | ~m1_subset_1(B_908, k1_zfmisc_1(A_909)) | v1_xboole_0(A_909))), inference(cnfTransformation, [status(thm)], [f_81])).
% 49.26/36.91  tff(c_16529, plain, (![A_28]: (v1_subset_1('#skF_2'(A_28), A_28) | ~v1_xboole_0('#skF_2'(A_28)) | v1_xboole_0(A_28))), inference(resolution, [status(thm)], [c_30, c_16511])).
% 49.26/36.91  tff(c_16556, plain, (![A_910]: (~v1_xboole_0('#skF_2'(A_910)) | v1_xboole_0(A_910))), inference(negUnitSimplification, [status(thm)], [c_28, c_16529])).
% 49.26/36.91  tff(c_16566, plain, (![B_912, A_913]: (v1_xboole_0(k2_zfmisc_1(B_912, A_913)) | ~v1_xboole_0(A_913))), inference(resolution, [status(thm)], [c_520, c_16556])).
% 49.26/36.91  tff(c_274, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_154, c_249])).
% 49.26/36.91  tff(c_284, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(splitLeft, [status(thm)], [c_274])).
% 49.26/36.91  tff(c_16583, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_16566, c_284])).
% 49.26/36.91  tff(c_16591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16433, c_16583])).
% 49.26/36.91  tff(c_16593, plain, (v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(splitRight, [status(thm)], [c_274])).
% 49.26/36.91  tff(c_16690, plain, (![C_925, B_926, A_927]: (~v1_xboole_0(C_925) | ~m1_subset_1(B_926, k1_zfmisc_1(C_925)) | ~r2_hidden(A_927, B_926))), inference(cnfTransformation, [status(thm)], [f_119])).
% 49.26/36.91  tff(c_16704, plain, (![A_927]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5')) | ~r2_hidden(A_927, '#skF_6'))), inference(resolution, [status(thm)], [c_162, c_16690])).
% 49.26/36.91  tff(c_16717, plain, (![A_927]: (~r2_hidden(A_927, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_16593, c_16704])).
% 49.26/36.91  tff(c_137234, plain, (![C_5455, A_5456]: (r1_tarski('#skF_6', C_5455) | ~m1_subset_1(C_5455, k1_zfmisc_1(A_5456)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_5456)))), inference(resolution, [status(thm)], [c_137154, c_16717])).
% 49.26/36.91  tff(c_137271, plain, (![A_10]: (r1_tarski('#skF_6', k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_10, c_137234])).
% 49.26/36.91  tff(c_137278, plain, (![A_10]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(splitLeft, [status(thm)], [c_137271])).
% 49.26/36.91  tff(c_137280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137278, c_162])).
% 49.26/36.91  tff(c_137281, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_137271])).
% 49.26/36.91  tff(c_206, plain, (![A_146, B_147]: (r1_tarski(A_146, B_147) | ~m1_subset_1(A_146, k1_zfmisc_1(B_147)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 49.26/36.91  tff(c_230, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(resolution, [status(thm)], [c_10, c_206])).
% 49.26/36.91  tff(c_138294, plain, (![C_5496, A_5497, B_5498]: (r1_tarski(C_5496, k3_subset_1(A_5497, B_5498)) | ~r1_tarski(B_5498, k3_subset_1(A_5497, C_5496)) | ~m1_subset_1(C_5496, k1_zfmisc_1(A_5497)) | ~m1_subset_1(B_5498, k1_zfmisc_1(A_5497)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 49.26/36.91  tff(c_138318, plain, (![C_5496, A_5497]: (r1_tarski(C_5496, k3_subset_1(A_5497, k1_xboole_0)) | ~m1_subset_1(C_5496, k1_zfmisc_1(A_5497)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5497)))), inference(resolution, [status(thm)], [c_230, c_138294])).
% 49.26/36.91  tff(c_138507, plain, (![C_5504, A_5505]: (r1_tarski(C_5504, k3_subset_1(A_5505, k1_xboole_0)) | ~m1_subset_1(C_5504, k1_zfmisc_1(A_5505)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138318])).
% 49.26/36.91  tff(c_8, plain, (![B_8, A_7, C_9]: (k1_xboole_0=B_8 | ~r1_tarski(B_8, k3_subset_1(A_7, C_9)) | ~r1_tarski(B_8, C_9) | ~m1_subset_1(C_9, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 49.26/36.91  tff(c_138520, plain, (![C_5504, A_5505]: (k1_xboole_0=C_5504 | ~r1_tarski(C_5504, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5505)) | ~m1_subset_1(C_5504, k1_zfmisc_1(A_5505)))), inference(resolution, [status(thm)], [c_138507, c_8])).
% 49.26/36.91  tff(c_138591, plain, (![C_5510, A_5511]: (k1_xboole_0=C_5510 | ~r1_tarski(C_5510, k1_xboole_0) | ~m1_subset_1(C_5510, k1_zfmisc_1(A_5511)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_138520])).
% 49.26/36.91  tff(c_138627, plain, (k1_xboole_0='#skF_6' | ~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_138591])).
% 49.26/36.91  tff(c_138645, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_137281, c_138627])).
% 49.26/36.91  tff(c_16700, plain, (![A_927]: (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5')) | ~r2_hidden(A_927, '#skF_7'))), inference(resolution, [status(thm)], [c_154, c_16690])).
% 49.26/36.91  tff(c_16713, plain, (![A_927]: (~r2_hidden(A_927, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_16593, c_16700])).
% 49.26/36.91  tff(c_137316, plain, (![C_5462, A_5463]: (r1_tarski('#skF_7', C_5462) | ~m1_subset_1(C_5462, k1_zfmisc_1(A_5463)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_5463)))), inference(resolution, [status(thm)], [c_137154, c_16713])).
% 49.26/36.91  tff(c_137353, plain, (![A_10]: (r1_tarski('#skF_7', k1_xboole_0) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_10, c_137316])).
% 49.26/36.91  tff(c_137360, plain, (![A_10]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(splitLeft, [status(thm)], [c_137353])).
% 49.26/36.91  tff(c_137362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_137360, c_154])).
% 49.26/36.91  tff(c_137363, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_137353])).
% 49.26/36.91  tff(c_138621, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_138591])).
% 49.26/36.91  tff(c_138641, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_137363, c_138621])).
% 49.26/36.91  tff(c_138719, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_138645, c_138641])).
% 49.26/36.91  tff(c_16902, plain, (![A_978, B_979, D_980]: (r2_relset_1(A_978, B_979, D_980, D_980) | ~m1_subset_1(D_980, k1_zfmisc_1(k2_zfmisc_1(A_978, B_979))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 49.26/36.91  tff(c_16929, plain, (![A_978, B_979]: (r2_relset_1(A_978, B_979, k1_xboole_0, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_16902])).
% 49.26/36.91  tff(c_138697, plain, (![A_978, B_979]: (r2_relset_1(A_978, B_979, '#skF_7', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_138641, c_138641, c_16929])).
% 49.26/36.91  tff(c_141164, plain, (![A_978, B_979]: (r2_relset_1(A_978, B_979, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138719, c_138697])).
% 49.26/36.91  tff(c_138704, plain, (![A_10]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_138641, c_10])).
% 49.26/36.91  tff(c_140861, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138704])).
% 49.26/36.91  tff(c_27382, plain, (![A_1539, B_1540, C_1541]: (k2_relset_1(A_1539, B_1540, C_1541)=k2_relat_1(C_1541) | ~m1_subset_1(C_1541, k1_zfmisc_1(k2_zfmisc_1(A_1539, B_1540))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 49.26/36.91  tff(c_27427, plain, (![A_1539, B_1540]: (k2_relset_1(A_1539, B_1540, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_27382])).
% 49.26/36.91  tff(c_138694, plain, (![A_1539, B_1540]: (k2_relset_1(A_1539, B_1540, '#skF_7')=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_138641, c_138641, c_27427])).
% 49.26/36.91  tff(c_141343, plain, (![A_1539, B_1540]: (k2_relset_1(A_1539, B_1540, '#skF_6')=k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138719, c_138694])).
% 49.26/36.91  tff(c_140601, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6'), k6_partfun1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_152])).
% 49.26/36.91  tff(c_152923, plain, (![A_6106, B_6107, C_6108, D_6109]: (k2_relset_1(A_6106, B_6107, C_6108)=B_6107 | ~r2_relset_1(B_6107, B_6107, k1_partfun1(B_6107, A_6106, A_6106, B_6107, D_6109, C_6108), k6_partfun1(B_6107)) | ~m1_subset_1(D_6109, k1_zfmisc_1(k2_zfmisc_1(B_6107, A_6106))) | ~v1_funct_2(D_6109, B_6107, A_6106) | ~v1_funct_1(D_6109) | ~m1_subset_1(C_6108, k1_zfmisc_1(k2_zfmisc_1(A_6106, B_6107))) | ~v1_funct_2(C_6108, A_6106, B_6107) | ~v1_funct_1(C_6108))), inference(cnfTransformation, [status(thm)], [f_336])).
% 49.26/36.91  tff(c_152926, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_140601, c_152923])).
% 49.26/36.91  tff(c_152929, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_140861, c_141343, c_152926])).
% 49.26/36.91  tff(c_152930, plain, (![A_1539, B_1540]: (k2_relset_1(A_1539, B_1540, '#skF_6')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_152929, c_141343])).
% 49.26/36.91  tff(c_16925, plain, (![A_93]: (r2_relset_1(A_93, A_93, k6_partfun1(A_93), k6_partfun1(A_93)))), inference(resolution, [status(thm)], [c_122, c_16902])).
% 49.26/36.91  tff(c_28071, plain, (![C_1618, A_1619, B_1620]: (v2_funct_1(C_1618) | ~v3_funct_2(C_1618, A_1619, B_1620) | ~v1_funct_1(C_1618) | ~m1_subset_1(C_1618, k1_zfmisc_1(k2_zfmisc_1(A_1619, B_1620))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 49.26/36.91  tff(c_28102, plain, (v2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_28071])).
% 49.26/36.91  tff(c_28119, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_164, c_28102])).
% 49.26/36.91  tff(c_141937, plain, (![A_5659, B_5660, C_5661, D_5662]: (k2_relset_1(A_5659, B_5660, C_5661)=B_5660 | ~r2_relset_1(B_5660, B_5660, k1_partfun1(B_5660, A_5659, A_5659, B_5660, D_5662, C_5661), k6_partfun1(B_5660)) | ~m1_subset_1(D_5662, k1_zfmisc_1(k2_zfmisc_1(B_5660, A_5659))) | ~v1_funct_2(D_5662, B_5660, A_5659) | ~v1_funct_1(D_5662) | ~m1_subset_1(C_5661, k1_zfmisc_1(k2_zfmisc_1(A_5659, B_5660))) | ~v1_funct_2(C_5661, A_5659, B_5660) | ~v1_funct_1(C_5661))), inference(cnfTransformation, [status(thm)], [f_336])).
% 49.26/36.91  tff(c_141940, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_140601, c_141937])).
% 49.26/36.91  tff(c_141943, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_140861, c_141343, c_141940])).
% 49.26/36.91  tff(c_141944, plain, (![A_1539, B_1540]: (k2_relset_1(A_1539, B_1540, '#skF_6')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_141943, c_141343])).
% 49.26/36.91  tff(c_148, plain, (![C_120, D_122, B_119, A_118]: (k2_funct_1(C_120)=D_122 | k1_xboole_0=B_119 | k1_xboole_0=A_118 | ~v2_funct_1(C_120) | ~r2_relset_1(A_118, A_118, k1_partfun1(A_118, B_119, B_119, A_118, C_120, D_122), k6_partfun1(A_118)) | k2_relset_1(A_118, B_119, C_120)!=B_119 | ~m1_subset_1(D_122, k1_zfmisc_1(k2_zfmisc_1(B_119, A_118))) | ~v1_funct_2(D_122, B_119, A_118) | ~v1_funct_1(D_122) | ~m1_subset_1(C_120, k1_zfmisc_1(k2_zfmisc_1(A_118, B_119))) | ~v1_funct_2(C_120, A_118, B_119) | ~v1_funct_1(C_120))), inference(cnfTransformation, [status(thm)], [f_417])).
% 49.26/36.91  tff(c_147504, plain, (![C_5891, D_5892, B_5893, A_5894]: (k2_funct_1(C_5891)=D_5892 | B_5893='#skF_6' | A_5894='#skF_6' | ~v2_funct_1(C_5891) | ~r2_relset_1(A_5894, A_5894, k1_partfun1(A_5894, B_5893, B_5893, A_5894, C_5891, D_5892), k6_partfun1(A_5894)) | k2_relset_1(A_5894, B_5893, C_5891)!=B_5893 | ~m1_subset_1(D_5892, k1_zfmisc_1(k2_zfmisc_1(B_5893, A_5894))) | ~v1_funct_2(D_5892, B_5893, A_5894) | ~v1_funct_1(D_5892) | ~m1_subset_1(C_5891, k1_zfmisc_1(k2_zfmisc_1(A_5894, B_5893))) | ~v1_funct_2(C_5891, A_5894, B_5893) | ~v1_funct_1(C_5891))), inference(demodulation, [status(thm), theory('equality')], [c_138645, c_138645, c_148])).
% 49.26/36.91  tff(c_147507, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_140601, c_147504])).
% 49.26/36.91  tff(c_147510, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_140861, c_141944, c_28119, c_147507])).
% 49.26/36.91  tff(c_147511, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_147510])).
% 49.26/36.91  tff(c_138537, plain, (![D_5506, C_5507, A_5508, B_5509]: (D_5506=C_5507 | ~r2_relset_1(A_5508, B_5509, C_5507, D_5506) | ~m1_subset_1(D_5506, k1_zfmisc_1(k2_zfmisc_1(A_5508, B_5509))) | ~m1_subset_1(C_5507, k1_zfmisc_1(k2_zfmisc_1(A_5508, B_5509))))), inference(cnfTransformation, [status(thm)], [f_209])).
% 49.26/36.91  tff(c_138555, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7')=k6_partfun1('#skF_5') | ~m1_subset_1(k6_partfun1('#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_152, c_138537])).
% 49.26/36.91  tff(c_138590, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_7'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_138555])).
% 49.26/36.91  tff(c_141846, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6')=k6_partfun1('#skF_5') | ~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138719, c_138590])).
% 49.26/36.91  tff(c_141847, plain, (~m1_subset_1(k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(splitLeft, [status(thm)], [c_141846])).
% 49.26/36.91  tff(c_152727, plain, (~m1_subset_1(k1_partfun1('#skF_6', '#skF_6', '#skF_6', '#skF_6', '#skF_6', '#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_147511, c_147511, c_147511, c_147511, c_147511, c_147511, c_141847])).
% 49.26/36.91  tff(c_152730, plain, (~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_108, c_152727])).
% 49.26/36.91  tff(c_152737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_168, c_140861, c_152730])).
% 49.26/36.91  tff(c_152738, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_147510])).
% 49.26/36.91  tff(c_140804, plain, (![A_5588, B_5589]: (k2_funct_2(A_5588, B_5589)=k2_funct_1(B_5589) | ~m1_subset_1(B_5589, k1_zfmisc_1(k2_zfmisc_1(A_5588, A_5588))) | ~v3_funct_2(B_5589, A_5588, A_5588) | ~v1_funct_2(B_5589, A_5588, A_5588) | ~v1_funct_1(B_5589))), inference(cnfTransformation, [status(thm)], [f_319])).
% 49.26/36.91  tff(c_140837, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_140804])).
% 49.26/36.91  tff(c_140848, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_164, c_140837])).
% 49.26/36.91  tff(c_140602, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', k2_funct_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_150])).
% 49.26/36.91  tff(c_141023, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_140848, c_140602])).
% 49.26/36.91  tff(c_152829, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_152738, c_141023])).
% 49.26/36.91  tff(c_152843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141164, c_152829])).
% 49.26/36.91  tff(c_152844, plain, (k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6')=k6_partfun1('#skF_5')), inference(splitRight, [status(thm)], [c_141846])).
% 49.26/36.91  tff(c_194083, plain, (![C_7080, D_7081, B_7082, A_7083]: (k2_funct_1(C_7080)=D_7081 | B_7082='#skF_6' | A_7083='#skF_6' | ~v2_funct_1(C_7080) | ~r2_relset_1(A_7083, A_7083, k1_partfun1(A_7083, B_7082, B_7082, A_7083, C_7080, D_7081), k6_partfun1(A_7083)) | k2_relset_1(A_7083, B_7082, C_7080)!=B_7082 | ~m1_subset_1(D_7081, k1_zfmisc_1(k2_zfmisc_1(B_7082, A_7083))) | ~v1_funct_2(D_7081, B_7082, A_7083) | ~v1_funct_1(D_7081) | ~m1_subset_1(C_7080, k1_zfmisc_1(k2_zfmisc_1(A_7083, B_7082))) | ~v1_funct_2(C_7080, A_7083, B_7082) | ~v1_funct_1(C_7080))), inference(demodulation, [status(thm), theory('equality')], [c_138645, c_138645, c_148])).
% 49.26/36.91  tff(c_194086, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6' | '#skF_5'='#skF_6' | ~v2_funct_1('#skF_6') | ~r2_relset_1('#skF_5', '#skF_5', k6_partfun1('#skF_5'), k6_partfun1('#skF_5')) | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_152844, c_194083])).
% 49.26/36.91  tff(c_194088, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_140861, c_168, c_166, c_140861, c_152930, c_16925, c_28119, c_194086])).
% 49.26/36.91  tff(c_194089, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_194088])).
% 49.26/36.91  tff(c_141175, plain, (![A_5603, B_5604]: (m1_subset_1(k2_funct_2(A_5603, B_5604), k1_zfmisc_1(k2_zfmisc_1(A_5603, A_5603))) | ~m1_subset_1(B_5604, k1_zfmisc_1(k2_zfmisc_1(A_5603, A_5603))) | ~v3_funct_2(B_5604, A_5603, A_5603) | ~v1_funct_2(B_5604, A_5603, A_5603) | ~v1_funct_1(B_5604))), inference(cnfTransformation, [status(thm)], [f_294])).
% 49.26/36.91  tff(c_141224, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_140848, c_141175])).
% 49.26/36.91  tff(c_141243, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_164, c_140861, c_141224])).
% 49.26/36.91  tff(c_194098, plain, (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_194089, c_194089, c_141243])).
% 49.26/36.91  tff(c_138700, plain, (![A_10]: (r1_tarski('#skF_7', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_138641, c_230])).
% 49.26/36.91  tff(c_140684, plain, (![A_10]: (r1_tarski('#skF_6', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138700])).
% 49.26/36.91  tff(c_137250, plain, (r1_tarski('#skF_6', '#skF_7') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5')))), inference(resolution, [status(thm)], [c_154, c_137234])).
% 49.26/36.91  tff(c_137266, plain, (r1_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_137250])).
% 49.26/36.91  tff(c_138042, plain, (![D_5490, B_5488, E_5487, C_5489, A_5486]: (m1_subset_1(E_5487, k1_zfmisc_1(k2_zfmisc_1(B_5488, D_5490))) | ~r1_tarski(C_5489, D_5490) | ~r1_tarski(A_5486, B_5488) | ~m1_subset_1(E_5487, k1_zfmisc_1(k2_zfmisc_1(A_5486, C_5489))))), inference(cnfTransformation, [status(thm)], [f_217])).
% 49.26/36.91  tff(c_138113, plain, (![E_5487, B_5488, A_5486]: (m1_subset_1(E_5487, k1_zfmisc_1(k2_zfmisc_1(B_5488, '#skF_7'))) | ~r1_tarski(A_5486, B_5488) | ~m1_subset_1(E_5487, k1_zfmisc_1(k2_zfmisc_1(A_5486, '#skF_6'))))), inference(resolution, [status(thm)], [c_137266, c_138042])).
% 49.26/36.91  tff(c_195031, plain, (![E_7115, B_7116, A_7117]: (m1_subset_1(E_7115, k1_zfmisc_1(k2_zfmisc_1(B_7116, '#skF_6'))) | ~r1_tarski(A_7117, B_7116) | ~m1_subset_1(E_7115, k1_zfmisc_1(k2_zfmisc_1(A_7117, '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_138719, c_138113])).
% 49.26/36.91  tff(c_219889, plain, (![E_7750, A_7751]: (m1_subset_1(E_7750, k1_zfmisc_1(k2_zfmisc_1(A_7751, '#skF_6'))) | ~m1_subset_1(E_7750, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))))), inference(resolution, [status(thm)], [c_140684, c_195031])).
% 49.26/36.91  tff(c_220519, plain, (![A_7758]: (m1_subset_1(k2_funct_1('#skF_6'), k1_zfmisc_1(k2_zfmisc_1(A_7758, '#skF_6'))))), inference(resolution, [status(thm)], [c_194098, c_219889])).
% 49.26/36.91  tff(c_32, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 49.26/36.91  tff(c_220677, plain, (![A_7759]: (r1_tarski(k2_funct_1('#skF_6'), k2_zfmisc_1(A_7759, '#skF_6')))), inference(resolution, [status(thm)], [c_220519, c_32])).
% 49.26/36.91  tff(c_34, plain, (![A_30, B_31]: (m1_subset_1(A_30, k1_zfmisc_1(B_31)) | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_106])).
% 49.26/36.91  tff(c_27900, plain, (![C_1609, A_1610]: (k1_xboole_0=C_1609 | ~v1_funct_2(C_1609, A_1610, k1_xboole_0) | k1_xboole_0=A_1610 | ~m1_subset_1(C_1609, k1_zfmisc_1(k2_zfmisc_1(A_1610, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_266])).
% 49.26/36.91  tff(c_27938, plain, (![A_30, A_1610]: (k1_xboole_0=A_30 | ~v1_funct_2(A_30, A_1610, k1_xboole_0) | k1_xboole_0=A_1610 | ~r1_tarski(A_30, k2_zfmisc_1(A_1610, k1_xboole_0)))), inference(resolution, [status(thm)], [c_34, c_27900])).
% 49.26/36.91  tff(c_196611, plain, (![A_30, A_1610]: (A_30='#skF_6' | ~v1_funct_2(A_30, A_1610, '#skF_6') | A_1610='#skF_6' | ~r1_tarski(A_30, k2_zfmisc_1(A_1610, '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_138645, c_138645, c_138645, c_138645, c_27938])).
% 49.26/36.91  tff(c_220740, plain, (![A_7759]: (k2_funct_1('#skF_6')='#skF_6' | ~v1_funct_2(k2_funct_1('#skF_6'), A_7759, '#skF_6') | A_7759='#skF_6')), inference(resolution, [status(thm)], [c_220677, c_196611])).
% 49.26/36.91  tff(c_227475, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitLeft, [status(thm)], [c_220740])).
% 49.26/36.91  tff(c_194103, plain, (~r2_relset_1('#skF_6', '#skF_6', '#skF_6', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_194089, c_194089, c_141023])).
% 49.26/36.91  tff(c_227498, plain, (~r2_relset_1('#skF_6', '#skF_6', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_227475, c_194103])).
% 49.26/36.91  tff(c_227524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141164, c_227498])).
% 49.26/36.91  tff(c_227526, plain, (k2_funct_1('#skF_6')!='#skF_6'), inference(splitRight, [status(thm)], [c_220740])).
% 49.26/36.91  tff(c_19825, plain, (![A_1211, B_1212, C_1213]: (r2_hidden('#skF_1'(A_1211, B_1212, C_1213), B_1212) | r1_tarski(B_1212, C_1213) | ~m1_subset_1(C_1213, k1_zfmisc_1(A_1211)) | ~m1_subset_1(B_1212, k1_zfmisc_1(A_1211)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 49.26/36.91  tff(c_19929, plain, (![C_1219, A_1220]: (r1_tarski('#skF_6', C_1219) | ~m1_subset_1(C_1219, k1_zfmisc_1(A_1220)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_1220)))), inference(resolution, [status(thm)], [c_19825, c_16717])).
% 49.26/36.91  tff(c_19966, plain, (![A_10]: (r1_tarski('#skF_6', k1_xboole_0) | ~m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_10, c_19929])).
% 49.26/36.91  tff(c_19973, plain, (![A_10]: (~m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(splitLeft, [status(thm)], [c_19966])).
% 49.26/36.91  tff(c_19975, plain, $false, inference(negUnitSimplification, [status(thm)], [c_19973, c_162])).
% 49.26/36.91  tff(c_19976, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(splitRight, [status(thm)], [c_19966])).
% 49.26/36.91  tff(c_20893, plain, (![C_1260, A_1261, B_1262]: (r1_tarski(C_1260, k3_subset_1(A_1261, B_1262)) | ~r1_tarski(B_1262, k3_subset_1(A_1261, C_1260)) | ~m1_subset_1(C_1260, k1_zfmisc_1(A_1261)) | ~m1_subset_1(B_1262, k1_zfmisc_1(A_1261)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 49.26/36.91  tff(c_20914, plain, (![C_1260, A_1261]: (r1_tarski(C_1260, k3_subset_1(A_1261, k1_xboole_0)) | ~m1_subset_1(C_1260, k1_zfmisc_1(A_1261)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1261)))), inference(resolution, [status(thm)], [c_230, c_20893])).
% 49.26/36.91  tff(c_25098, plain, (![C_1407, A_1408]: (r1_tarski(C_1407, k3_subset_1(A_1408, k1_xboole_0)) | ~m1_subset_1(C_1407, k1_zfmisc_1(A_1408)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20914])).
% 49.26/36.91  tff(c_25109, plain, (![C_1407, A_1408]: (k1_xboole_0=C_1407 | ~r1_tarski(C_1407, k1_xboole_0) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1408)) | ~m1_subset_1(C_1407, k1_zfmisc_1(A_1408)))), inference(resolution, [status(thm)], [c_25098, c_8])).
% 49.26/36.91  tff(c_25123, plain, (![C_1409, A_1410]: (k1_xboole_0=C_1409 | ~r1_tarski(C_1409, k1_xboole_0) | ~m1_subset_1(C_1409, k1_zfmisc_1(A_1410)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_25109])).
% 49.26/36.91  tff(c_25159, plain, (k1_xboole_0='#skF_6' | ~r1_tarski('#skF_6', k1_xboole_0)), inference(resolution, [status(thm)], [c_162, c_25123])).
% 49.26/36.91  tff(c_25177, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_19976, c_25159])).
% 49.26/36.91  tff(c_20063, plain, (![C_1229, A_1230]: (r1_tarski('#skF_7', C_1229) | ~m1_subset_1(C_1229, k1_zfmisc_1(A_1230)) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_1230)))), inference(resolution, [status(thm)], [c_19825, c_16713])).
% 49.26/36.91  tff(c_20100, plain, (![A_10]: (r1_tarski('#skF_7', k1_xboole_0) | ~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(resolution, [status(thm)], [c_10, c_20063])).
% 49.26/36.91  tff(c_20107, plain, (![A_10]: (~m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(splitLeft, [status(thm)], [c_20100])).
% 49.26/36.91  tff(c_20109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20107, c_154])).
% 49.26/36.91  tff(c_20110, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_20100])).
% 49.26/36.91  tff(c_25153, plain, (k1_xboole_0='#skF_7' | ~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_154, c_25123])).
% 49.26/36.91  tff(c_25173, plain, (k1_xboole_0='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_20110, c_25153])).
% 49.26/36.91  tff(c_25260, plain, ('#skF_7'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_25177, c_25173])).
% 49.26/36.91  tff(c_25238, plain, (![A_978, B_979]: (r2_relset_1(A_978, B_979, '#skF_7', '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25173, c_25173, c_16929])).
% 49.26/36.91  tff(c_25892, plain, (![A_978, B_979]: (r2_relset_1(A_978, B_979, '#skF_6', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25260, c_25260, c_25238])).
% 49.26/36.91  tff(c_276, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_5'))), inference(resolution, [status(thm)], [c_162, c_249])).
% 49.26/36.91  tff(c_16595, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16593, c_276])).
% 49.26/36.91  tff(c_25245, plain, (![A_10]: (m1_subset_1('#skF_7', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_25173, c_10])).
% 49.26/36.91  tff(c_25575, plain, (![A_10]: (m1_subset_1('#skF_6', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_25260, c_25245])).
% 49.26/36.91  tff(c_17144, plain, (![A_1003, B_1004, C_1005]: (k2_relset_1(A_1003, B_1004, C_1005)=k2_relat_1(C_1005) | ~m1_subset_1(C_1005, k1_zfmisc_1(k2_zfmisc_1(A_1003, B_1004))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 49.26/36.91  tff(c_17189, plain, (![A_1003, B_1004]: (k2_relset_1(A_1003, B_1004, k1_xboole_0)=k2_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_17144])).
% 49.26/36.91  tff(c_25235, plain, (![A_1003, B_1004]: (k2_relset_1(A_1003, B_1004, '#skF_7')=k2_relat_1('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_25173, c_25173, c_17189])).
% 49.26/36.91  tff(c_26015, plain, (![A_1003, B_1004]: (k2_relset_1(A_1003, B_1004, '#skF_6')=k2_relat_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25260, c_25260, c_25235])).
% 49.26/36.91  tff(c_25335, plain, (r2_relset_1('#skF_5', '#skF_5', k1_partfun1('#skF_5', '#skF_5', '#skF_5', '#skF_5', '#skF_6', '#skF_6'), k6_partfun1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_25260, c_152])).
% 49.26/36.91  tff(c_26664, plain, (![A_1478, B_1479, C_1480, D_1481]: (k2_relset_1(A_1478, B_1479, C_1480)=B_1479 | ~r2_relset_1(B_1479, B_1479, k1_partfun1(B_1479, A_1478, A_1478, B_1479, D_1481, C_1480), k6_partfun1(B_1479)) | ~m1_subset_1(D_1481, k1_zfmisc_1(k2_zfmisc_1(B_1479, A_1478))) | ~v1_funct_2(D_1481, B_1479, A_1478) | ~v1_funct_1(D_1481) | ~m1_subset_1(C_1480, k1_zfmisc_1(k2_zfmisc_1(A_1478, B_1479))) | ~v1_funct_2(C_1480, A_1478, B_1479) | ~v1_funct_1(C_1480))), inference(cnfTransformation, [status(thm)], [f_336])).
% 49.26/36.91  tff(c_26667, plain, (k2_relset_1('#skF_5', '#skF_5', '#skF_6')='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_25335, c_26664])).
% 49.26/36.91  tff(c_26670, plain, (k2_relat_1('#skF_6')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_25575, c_26015, c_26667])).
% 49.26/36.91  tff(c_26671, plain, (![A_1003, B_1004]: (k2_relset_1(A_1003, B_1004, '#skF_6')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26670, c_26015])).
% 49.26/36.91  tff(c_17860, plain, (![C_1080, A_1081, B_1082]: (v2_funct_1(C_1080) | ~v3_funct_2(C_1080, A_1081, B_1082) | ~v1_funct_1(C_1080) | ~m1_subset_1(C_1080, k1_zfmisc_1(k2_zfmisc_1(A_1081, B_1082))))), inference(cnfTransformation, [status(thm)], [f_248])).
% 49.26/36.91  tff(c_17895, plain, (v2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_17860])).
% 49.26/36.91  tff(c_17913, plain, (v2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_164, c_17895])).
% 49.26/36.91  tff(c_27118, plain, (![C_1518, D_1519, B_1520, A_1521]: (k2_funct_1(C_1518)=D_1519 | B_1520='#skF_6' | A_1521='#skF_6' | ~v2_funct_1(C_1518) | ~r2_relset_1(A_1521, A_1521, k1_partfun1(A_1521, B_1520, B_1520, A_1521, C_1518, D_1519), k6_partfun1(A_1521)) | k2_relset_1(A_1521, B_1520, C_1518)!=B_1520 | ~m1_subset_1(D_1519, k1_zfmisc_1(k2_zfmisc_1(B_1520, A_1521))) | ~v1_funct_2(D_1519, B_1520, A_1521) | ~v1_funct_1(D_1519) | ~m1_subset_1(C_1518, k1_zfmisc_1(k2_zfmisc_1(A_1521, B_1520))) | ~v1_funct_2(C_1518, A_1521, B_1520) | ~v1_funct_1(C_1518))), inference(demodulation, [status(thm), theory('equality')], [c_25177, c_25177, c_148])).
% 49.26/36.91  tff(c_27121, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6' | ~v2_funct_1('#skF_6') | k2_relset_1('#skF_5', '#skF_5', '#skF_6')!='#skF_5' | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_5', '#skF_5'))) | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_25335, c_27118])).
% 49.26/36.91  tff(c_27124, plain, (k2_funct_1('#skF_6')='#skF_6' | '#skF_5'='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_25575, c_26671, c_17913, c_27121])).
% 49.26/36.91  tff(c_27125, plain, ('#skF_5'='#skF_6'), inference(splitLeft, [status(thm)], [c_27124])).
% 49.26/36.91  tff(c_16930, plain, (![C_981, A_982, B_983]: (v1_partfun1(C_981, A_982) | ~m1_subset_1(C_981, k1_zfmisc_1(k2_zfmisc_1(A_982, B_983))) | ~v1_xboole_0(A_982))), inference(cnfTransformation, [status(thm)], [f_236])).
% 49.26/36.91  tff(c_16963, plain, (v1_partfun1('#skF_7', '#skF_5') | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_154, c_16930])).
% 49.26/36.91  tff(c_16968, plain, (~v1_xboole_0('#skF_5')), inference(splitLeft, [status(thm)], [c_16963])).
% 49.26/36.91  tff(c_27145, plain, (~v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27125, c_16968])).
% 49.26/36.91  tff(c_27156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16595, c_27145])).
% 49.26/36.91  tff(c_27157, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_27124])).
% 49.26/36.91  tff(c_25265, plain, (![A_1411, B_1412]: (k2_funct_2(A_1411, B_1412)=k2_funct_1(B_1412) | ~m1_subset_1(B_1412, k1_zfmisc_1(k2_zfmisc_1(A_1411, A_1411))) | ~v3_funct_2(B_1412, A_1411, A_1411) | ~v1_funct_2(B_1412, A_1411, A_1411) | ~v1_funct_1(B_1412))), inference(cnfTransformation, [status(thm)], [f_319])).
% 49.26/36.91  tff(c_25301, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6') | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_25265])).
% 49.26/36.91  tff(c_25315, plain, (k2_funct_2('#skF_5', '#skF_6')=k2_funct_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_164, c_25301])).
% 49.26/36.91  tff(c_25336, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', k2_funct_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25260, c_150])).
% 49.26/36.91  tff(c_25721, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_25315, c_25336])).
% 49.26/36.91  tff(c_27209, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_27157, c_25721])).
% 49.26/36.91  tff(c_27223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_25892, c_27209])).
% 49.26/36.91  tff(c_27225, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_16963])).
% 49.26/36.91  tff(c_72, plain, (![C_58, B_56, A_55]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(B_56, A_55))) | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_197])).
% 49.26/36.91  tff(c_141717, plain, (v1_xboole_0(k2_funct_1('#skF_6')) | ~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_141243, c_72])).
% 49.26/36.91  tff(c_141770, plain, (v1_xboole_0(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_27225, c_141717])).
% 49.26/36.91  tff(c_137301, plain, (![A_5461]: (r1_tarski('#skF_6', k6_partfun1(A_5461)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(A_5461, A_5461))))), inference(resolution, [status(thm)], [c_122, c_137234])).
% 49.26/36.91  tff(c_137309, plain, (r1_tarski('#skF_6', k6_partfun1('#skF_5'))), inference(resolution, [status(thm)], [c_162, c_137301])).
% 49.26/36.91  tff(c_141404, plain, (![E_5621, B_5622, A_5623]: (m1_subset_1(E_5621, k1_zfmisc_1(k2_zfmisc_1(B_5622, k6_partfun1('#skF_5')))) | ~r1_tarski(A_5623, B_5622) | ~m1_subset_1(E_5621, k1_zfmisc_1(k2_zfmisc_1(A_5623, '#skF_6'))))), inference(resolution, [status(thm)], [c_137309, c_138042])).
% 49.26/36.91  tff(c_141425, plain, (![E_5621, A_10]: (m1_subset_1(E_5621, k1_zfmisc_1(k2_zfmisc_1(A_10, k6_partfun1('#skF_5')))) | ~m1_subset_1(E_5621, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))))), inference(resolution, [status(thm)], [c_140684, c_141404])).
% 49.26/36.91  tff(c_194339, plain, (![E_7092, A_7093]: (m1_subset_1(E_7092, k1_zfmisc_1(k2_zfmisc_1(A_7093, k6_partfun1('#skF_6')))) | ~m1_subset_1(E_7092, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))))), inference(demodulation, [status(thm), theory('equality')], [c_194089, c_141425])).
% 49.26/36.91  tff(c_88, plain, (![C_78, A_75, B_76]: (v1_partfun1(C_78, A_75) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))) | ~v1_xboole_0(A_75))), inference(cnfTransformation, [status(thm)], [f_236])).
% 49.26/36.91  tff(c_206445, plain, (![E_7436, A_7437]: (v1_partfun1(E_7436, A_7437) | ~v1_xboole_0(A_7437) | ~m1_subset_1(E_7436, k1_zfmisc_1(k2_zfmisc_1('#skF_6', '#skF_6'))))), inference(resolution, [status(thm)], [c_194339, c_88])).
% 49.26/36.91  tff(c_206487, plain, (![A_7437]: (v1_partfun1(k2_funct_1('#skF_6'), A_7437) | ~v1_xboole_0(A_7437))), inference(resolution, [status(thm)], [c_194098, c_206445])).
% 49.26/36.91  tff(c_140628, plain, (![A_5583, B_5584]: (v1_funct_1(k2_funct_2(A_5583, B_5584)) | ~m1_subset_1(B_5584, k1_zfmisc_1(k2_zfmisc_1(A_5583, A_5583))) | ~v3_funct_2(B_5584, A_5583, A_5583) | ~v1_funct_2(B_5584, A_5583, A_5583) | ~v1_funct_1(B_5584))), inference(cnfTransformation, [status(thm)], [f_294])).
% 49.26/36.91  tff(c_140661, plain, (v1_funct_1(k2_funct_2('#skF_5', '#skF_6')) | ~v3_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_2('#skF_6', '#skF_5', '#skF_5') | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_162, c_140628])).
% 49.26/36.91  tff(c_140672, plain, (v1_funct_1(k2_funct_2('#skF_5', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_168, c_166, c_164, c_140661])).
% 49.26/36.91  tff(c_141022, plain, (v1_funct_1(k2_funct_1('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_140848, c_140672])).
% 49.26/36.91  tff(c_84, plain, (![C_74, A_72, B_73]: (v1_funct_2(C_74, A_72, B_73) | ~v1_partfun1(C_74, A_72) | ~v1_funct_1(C_74) | ~m1_subset_1(C_74, k1_zfmisc_1(k2_zfmisc_1(A_72, B_73))))), inference(cnfTransformation, [status(thm)], [f_229])).
% 49.26/36.91  tff(c_220576, plain, (![A_7758]: (v1_funct_2(k2_funct_1('#skF_6'), A_7758, '#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), A_7758) | ~v1_funct_1(k2_funct_1('#skF_6')))), inference(resolution, [status(thm)], [c_220519, c_84])).
% 49.26/36.91  tff(c_220650, plain, (![A_7758]: (v1_funct_2(k2_funct_1('#skF_6'), A_7758, '#skF_6') | ~v1_partfun1(k2_funct_1('#skF_6'), A_7758))), inference(demodulation, [status(thm), theory('equality')], [c_141022, c_220576])).
% 49.26/36.91  tff(c_227579, plain, (![A_7891]: (~v1_funct_2(k2_funct_1('#skF_6'), A_7891, '#skF_6') | A_7891='#skF_6')), inference(splitRight, [status(thm)], [c_220740])).
% 49.26/36.91  tff(c_227589, plain, (![A_7892]: (A_7892='#skF_6' | ~v1_partfun1(k2_funct_1('#skF_6'), A_7892))), inference(resolution, [status(thm)], [c_220650, c_227579])).
% 49.26/36.91  tff(c_227599, plain, (![A_7893]: (A_7893='#skF_6' | ~v1_xboole_0(A_7893))), inference(resolution, [status(thm)], [c_206487, c_227589])).
% 49.26/36.91  tff(c_227644, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_141770, c_227599])).
% 49.26/36.91  tff(c_227692, plain, $false, inference(negUnitSimplification, [status(thm)], [c_227526, c_227644])).
% 49.26/36.91  tff(c_227693, plain, (k2_funct_1('#skF_6')='#skF_6'), inference(splitRight, [status(thm)], [c_194088])).
% 49.26/36.91  tff(c_227784, plain, (~r2_relset_1('#skF_5', '#skF_5', '#skF_6', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_227693, c_141023])).
% 49.26/36.91  tff(c_227798, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141164, c_227784])).
% 49.26/36.91  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 49.26/36.91  
% 49.26/36.91  Inference rules
% 49.26/36.91  ----------------------
% 49.26/36.91  #Ref     : 0
% 49.26/36.91  #Sup     : 50137
% 49.26/36.91  #Fact    : 0
% 49.26/36.91  #Define  : 0
% 49.26/36.91  #Split   : 319
% 49.26/36.91  #Chain   : 0
% 49.26/36.91  #Close   : 0
% 49.26/36.91  
% 49.26/36.91  Ordering : KBO
% 49.26/36.91  
% 49.26/36.91  Simplification rules
% 49.26/36.91  ----------------------
% 49.26/36.91  #Subsume      : 6929
% 49.26/36.91  #Demod        : 42777
% 49.26/36.91  #Tautology    : 17115
% 49.26/36.91  #SimpNegUnit  : 457
% 49.26/36.91  #BackRed      : 4593
% 49.26/36.91  
% 49.26/36.91  #Partial instantiations: 0
% 49.26/36.91  #Strategies tried      : 1
% 49.26/36.91  
% 49.26/36.91  Timing (in seconds)
% 49.26/36.91  ----------------------
% 49.26/36.92  Preprocessing        : 0.47
% 49.26/36.92  Parsing              : 0.25
% 49.26/36.92  CNF conversion       : 0.04
% 49.26/36.92  Main loop            : 35.60
% 49.26/36.92  Inferencing          : 7.26
% 49.26/36.92  Reduction            : 15.50
% 49.26/36.92  Demodulation         : 12.21
% 49.26/36.92  BG Simplification    : 0.60
% 49.26/36.92  Subsumption          : 9.69
% 49.26/36.92  Abstraction          : 0.84
% 49.26/36.92  MUC search           : 0.00
% 49.26/36.92  Cooper               : 0.00
% 49.26/36.92  Total                : 36.18
% 49.26/36.92  Index Insertion      : 0.00
% 49.26/36.92  Index Deletion       : 0.00
% 49.26/36.92  Index Matching       : 0.00
% 49.26/36.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
