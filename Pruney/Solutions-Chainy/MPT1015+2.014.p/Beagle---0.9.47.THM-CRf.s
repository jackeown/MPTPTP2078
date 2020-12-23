%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:39 EST 2020

% Result     : Theorem 22.88s
% Output     : CNFRefutation 23.23s
% Verified   : 
% Statistics : Number of formulae       :  319 (7747 expanded)
%              Number of leaves         :   62 (2640 expanded)
%              Depth                    :   24
%              Number of atoms          :  729 (22796 expanded)
%              Number of equality atoms :  179 (2427 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_relset_1,type,(
    k8_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(f_298,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => ! [C] :
            ( ( v1_funct_1(C)
              & v1_funct_2(C,A,A)
              & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
           => ( ( r2_relset_1(A,A,k1_partfun1(A,A,A,A,C,B),B)
                & v2_funct_1(B) )
             => r2_relset_1(A,A,C,k6_partfun1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_188,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_168,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_161,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_103,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v2_funct_1(A)
            & r1_tarski(B,k1_relat_1(A)) )
         => k9_relat_1(k2_funct_1(A),k9_relat_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t177_funct_1)).

tff(f_220,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_206,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_244,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_172,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_278,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_270,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_176,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_260,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( v2_funct_1(C)
          & k2_relset_1(A,B,C) = B )
       => ( v1_funct_1(k2_funct_1(C))
          & v1_funct_2(k2_funct_1(C),B,A)
          & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_84,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_222,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_138,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_118,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_128,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_153,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(f_210,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_114,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_453,plain,(
    ! [A_137,B_138,D_139] :
      ( r2_relset_1(A_137,B_138,D_139,D_139)
      | ~ m1_subset_1(D_139,k1_zfmisc_1(k2_zfmisc_1(A_137,B_138))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_461,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_453])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_208,plain,(
    ! [B_105,A_106] :
      ( v1_relat_1(B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_106))
      | ~ v1_relat_1(A_106) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_214,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_114,c_208])).

tff(c_223,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_214])).

tff(c_118,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_405,plain,(
    ! [C_132,B_133,A_134] :
      ( v1_xboole_0(C_132)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(B_133,A_134)))
      | ~ v1_xboole_0(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_416,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_405])).

tff(c_418,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_416])).

tff(c_308,plain,(
    ! [C_124,A_125,B_126] :
      ( v4_relat_1(C_124,A_125)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_319,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_308])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_323,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_319,c_24])).

tff(c_326,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_323])).

tff(c_20,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_343,plain,
    ( k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_20])).

tff(c_347,plain,(
    k9_relat_1('#skF_3','#skF_1') = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_343])).

tff(c_1330,plain,(
    ! [A_188,B_189] :
      ( k9_relat_1(k2_funct_1(A_188),k9_relat_1(A_188,B_189)) = B_189
      | ~ r1_tarski(B_189,k1_relat_1(A_188))
      | ~ v2_funct_1(A_188)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1366,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_1330])).

tff(c_1385,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_1366])).

tff(c_1600,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_116,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_124,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_122,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_120,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_110,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_3414,plain,(
    ! [C_266,D_267,E_264,B_265,A_262,F_263] :
      ( k1_partfun1(A_262,B_265,C_266,D_267,E_264,F_263) = k5_relat_1(E_264,F_263)
      | ~ m1_subset_1(F_263,k1_zfmisc_1(k2_zfmisc_1(C_266,D_267)))
      | ~ v1_funct_1(F_263)
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_265)))
      | ~ v1_funct_1(E_264) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_3430,plain,(
    ! [A_262,B_265,E_264] :
      ( k1_partfun1(A_262,B_265,'#skF_1','#skF_1',E_264,'#skF_2') = k5_relat_1(E_264,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_264,k1_zfmisc_1(k2_zfmisc_1(A_262,B_265)))
      | ~ v1_funct_1(E_264) ) ),
    inference(resolution,[status(thm)],[c_120,c_3414])).

tff(c_3663,plain,(
    ! [A_278,B_279,E_280] :
      ( k1_partfun1(A_278,B_279,'#skF_1','#skF_1',E_280,'#skF_2') = k5_relat_1(E_280,'#skF_2')
      | ~ m1_subset_1(E_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279)))
      | ~ v1_funct_1(E_280) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_3430])).

tff(c_3687,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_3663])).

tff(c_3710,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_3687])).

tff(c_112,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_1889,plain,(
    ! [D_207,C_208,A_209,B_210] :
      ( D_207 = C_208
      | ~ r2_relset_1(A_209,B_210,C_208,D_207)
      | ~ m1_subset_1(D_207,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ m1_subset_1(C_208,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1901,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_112,c_1889])).

tff(c_1924,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_1901])).

tff(c_1926,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1924])).

tff(c_3775,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3710,c_1926])).

tff(c_3786,plain,(
    ! [A_285,C_284,E_289,B_286,D_288,F_287] :
      ( m1_subset_1(k1_partfun1(A_285,B_286,C_284,D_288,E_289,F_287),k1_zfmisc_1(k2_zfmisc_1(A_285,D_288)))
      | ~ m1_subset_1(F_287,k1_zfmisc_1(k2_zfmisc_1(C_284,D_288)))
      | ~ v1_funct_1(F_287)
      | ~ m1_subset_1(E_289,k1_zfmisc_1(k2_zfmisc_1(A_285,B_286)))
      | ~ v1_funct_1(E_289) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_3838,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3710,c_3786])).

tff(c_3860,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_124,c_120,c_3838])).

tff(c_3861,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3775,c_3860])).

tff(c_3862,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1924])).

tff(c_6192,plain,(
    ! [A_380,B_379,C_376,E_377,D_378] :
      ( k1_xboole_0 = C_376
      | v2_funct_1(D_378)
      | ~ v2_funct_1(k1_partfun1(A_380,B_379,B_379,C_376,D_378,E_377))
      | ~ m1_subset_1(E_377,k1_zfmisc_1(k2_zfmisc_1(B_379,C_376)))
      | ~ v1_funct_2(E_377,B_379,C_376)
      | ~ v1_funct_1(E_377)
      | ~ m1_subset_1(D_378,k1_zfmisc_1(k2_zfmisc_1(A_380,B_379)))
      | ~ v1_funct_2(D_378,A_380,B_379)
      | ~ v1_funct_1(D_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_244])).

tff(c_6200,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3')
    | ~ v2_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3862,c_6192])).

tff(c_6209,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_114,c_124,c_122,c_120,c_110,c_6200])).

tff(c_6210,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_1600,c_6209])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6267,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6210,c_2])).

tff(c_6269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_418,c_6267])).

tff(c_6271,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_739,plain,(
    ! [A_148,B_149,C_150] :
      ( k1_relset_1(A_148,B_149,C_150) = k1_relat_1(C_150)
      | ~ m1_subset_1(C_150,k1_zfmisc_1(k2_zfmisc_1(A_148,B_149))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_755,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_739])).

tff(c_6639,plain,(
    ! [A_394,B_395] :
      ( k1_relset_1(A_394,A_394,B_395) = A_394
      | ~ m1_subset_1(B_395,k1_zfmisc_1(k2_zfmisc_1(A_394,A_394)))
      | ~ v1_funct_2(B_395,A_394,A_394)
      | ~ v1_funct_1(B_395) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_6648,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_6639])).

tff(c_6660,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_755,c_6648])).

tff(c_6315,plain,(
    ! [A_385,B_386] :
      ( k1_relset_1(A_385,A_385,B_386) = A_385
      | ~ m1_subset_1(B_386,k1_zfmisc_1(k2_zfmisc_1(A_385,A_385)))
      | ~ v1_funct_2(B_386,A_385,A_385)
      | ~ v1_funct_1(B_386) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_6324,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_6315])).

tff(c_6336,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_755,c_6324])).

tff(c_6270,plain,
    ( ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_6289,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6270])).

tff(c_6340,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6336,c_6289])).

tff(c_6345,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6340])).

tff(c_6347,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6270])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_6350,plain,
    ( k1_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6347,c_4])).

tff(c_6598,plain,(
    ~ r1_tarski(k1_relat_1('#skF_3'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_6350])).

tff(c_6664,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6660,c_6598])).

tff(c_6670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6664])).

tff(c_6671,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6350])).

tff(c_102,plain,(
    ! [A_82] :
      ( v1_funct_2(A_82,k1_relat_1(A_82),k2_relat_1(A_82))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_6689,plain,
    ( v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6671,c_102])).

tff(c_6699,plain,(
    v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_6689])).

tff(c_100,plain,(
    ! [A_82] :
      ( m1_subset_1(A_82,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_82),k2_relat_1(A_82))))
      | ~ v1_funct_1(A_82)
      | ~ v1_relat_1(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_6686,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_6671,c_100])).

tff(c_6697,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_6686])).

tff(c_66,plain,(
    ! [A_45,B_46,C_47] :
      ( k2_relset_1(A_45,B_46,C_47) = k2_relat_1(C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_6741,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6697,c_66])).

tff(c_9257,plain,(
    ! [C_494,A_495,B_496] :
      ( v1_funct_1(k2_funct_1(C_494))
      | k2_relset_1(A_495,B_496,C_494) != B_496
      | ~ v2_funct_1(C_494)
      | ~ m1_subset_1(C_494,k1_zfmisc_1(k2_zfmisc_1(A_495,B_496)))
      | ~ v1_funct_2(C_494,A_495,B_496)
      | ~ v1_funct_1(C_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_9263,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6697,c_9257])).

tff(c_9284,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_6699,c_6271,c_6741,c_9263])).

tff(c_32,plain,(
    ! [A_20] :
      ( v1_relat_1(k2_funct_1(A_20))
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( k9_relat_1(B_16,k2_relat_1(A_14)) = k2_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6346,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),k2_relat_1('#skF_3')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_6270])).

tff(c_6361,plain,
    ( k2_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_6346])).

tff(c_6367,plain,
    ( k2_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_6361])).

tff(c_8933,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6367])).

tff(c_8937,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_8933])).

tff(c_8941,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_8937])).

tff(c_8943,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6367])).

tff(c_237,plain,(
    ! [C_111,B_112,A_113] :
      ( v5_relat_1(C_111,B_112)
      | ~ m1_subset_1(C_111,k1_zfmisc_1(k2_zfmisc_1(A_113,B_112))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_248,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_114,c_237])).

tff(c_289,plain,(
    ! [B_120,A_121] :
      ( k2_relat_1(k7_relat_1(B_120,A_121)) = k9_relat_1(B_120,A_121)
      | ~ v1_relat_1(B_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14040,plain,(
    ! [B_629,A_630,A_631] :
      ( r1_tarski(k9_relat_1(B_629,A_630),A_631)
      | ~ v5_relat_1(k7_relat_1(B_629,A_630),A_631)
      | ~ v1_relat_1(k7_relat_1(B_629,A_630))
      | ~ v1_relat_1(B_629) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_16])).

tff(c_14082,plain,(
    ! [A_631] :
      ( r1_tarski(k9_relat_1('#skF_3','#skF_1'),A_631)
      | ~ v5_relat_1('#skF_3',A_631)
      | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_14040])).

tff(c_14111,plain,(
    ! [A_631] :
      ( r1_tarski(k2_relat_1('#skF_3'),A_631)
      | ~ v5_relat_1('#skF_3',A_631) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_223,c_326,c_347,c_14082])).

tff(c_642,plain,(
    ! [A_144,B_145,C_146] :
      ( k2_relset_1(A_144,B_145,C_146) = k2_relat_1(C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_654,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_642])).

tff(c_9629,plain,(
    ! [C_514,B_515,A_516] :
      ( v1_funct_2(k2_funct_1(C_514),B_515,A_516)
      | k2_relset_1(A_516,B_515,C_514) != B_515
      | ~ v2_funct_1(C_514)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_516,B_515)))
      | ~ v1_funct_2(C_514,A_516,B_515)
      | ~ v1_funct_1(C_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_9650,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_9629])).

tff(c_9672,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_6271,c_654,c_9650])).

tff(c_9677,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9672])).

tff(c_217,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_120,c_208])).

tff(c_226,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_217])).

tff(c_756,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_739])).

tff(c_6527,plain,(
    ! [A_392,B_393] :
      ( k1_relset_1(A_392,A_392,B_393) = A_392
      | ~ m1_subset_1(B_393,k1_zfmisc_1(k2_zfmisc_1(A_392,A_392)))
      | ~ v1_funct_2(B_393,A_392,A_392)
      | ~ v1_funct_1(B_393) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_6539,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_6527])).

tff(c_6551,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_756,c_6539])).

tff(c_1538,plain,(
    ! [A_200,B_201] :
      ( k1_relset_1(A_200,A_200,B_201) = A_200
      | ~ m1_subset_1(B_201,k1_zfmisc_1(k2_zfmisc_1(A_200,A_200)))
      | ~ v1_funct_2(B_201,A_200,A_200)
      | ~ v1_funct_1(B_201) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1550,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_120,c_1538])).

tff(c_1562,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_122,c_756,c_1550])).

tff(c_320,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_308])).

tff(c_329,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_320,c_24])).

tff(c_332,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_329])).

tff(c_366,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_20])).

tff(c_370,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_366])).

tff(c_1363,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_1330])).

tff(c_1383,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_110,c_1363])).

tff(c_1444,plain,(
    ~ r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_1383])).

tff(c_1589,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1562,c_1444])).

tff(c_1594,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1589])).

tff(c_1596,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_1383])).

tff(c_1599,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1596,c_4])).

tff(c_6368,plain,(
    ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1599])).

tff(c_6552,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6551,c_6368])).

tff(c_6558,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6552])).

tff(c_6559,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1599])).

tff(c_1595,plain,(
    k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_1383])).

tff(c_8486,plain,(
    ! [C_461,E_459,F_458,B_460,D_462,A_457] :
      ( k1_partfun1(A_457,B_460,C_461,D_462,E_459,F_458) = k5_relat_1(E_459,F_458)
      | ~ m1_subset_1(F_458,k1_zfmisc_1(k2_zfmisc_1(C_461,D_462)))
      | ~ v1_funct_1(F_458)
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_460)))
      | ~ v1_funct_1(E_459) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_8504,plain,(
    ! [A_457,B_460,E_459] :
      ( k1_partfun1(A_457,B_460,'#skF_1','#skF_1',E_459,'#skF_2') = k5_relat_1(E_459,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_459,k1_zfmisc_1(k2_zfmisc_1(A_457,B_460)))
      | ~ v1_funct_1(E_459) ) ),
    inference(resolution,[status(thm)],[c_120,c_8486])).

tff(c_8567,plain,(
    ! [A_465,B_466,E_467] :
      ( k1_partfun1(A_465,B_466,'#skF_1','#skF_1',E_467,'#skF_2') = k5_relat_1(E_467,'#skF_2')
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(A_465,B_466)))
      | ~ v1_funct_1(E_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_8504])).

tff(c_8591,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_8567])).

tff(c_8614,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_8591])).

tff(c_6831,plain,(
    ! [D_398,C_399,A_400,B_401] :
      ( D_398 = C_399
      | ~ r2_relset_1(A_400,B_401,C_399,D_398)
      | ~ m1_subset_1(D_398,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_6843,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_112,c_6831])).

tff(c_6866,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_6843])).

tff(c_6877,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_6866])).

tff(c_8645,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8614,c_6877])).

tff(c_8656,plain,(
    ! [A_470,C_469,B_471,F_472,E_474,D_473] :
      ( m1_subset_1(k1_partfun1(A_470,B_471,C_469,D_473,E_474,F_472),k1_zfmisc_1(k2_zfmisc_1(A_470,D_473)))
      | ~ m1_subset_1(F_472,k1_zfmisc_1(k2_zfmisc_1(C_469,D_473)))
      | ~ v1_funct_1(F_472)
      | ~ m1_subset_1(E_474,k1_zfmisc_1(k2_zfmisc_1(A_470,B_471)))
      | ~ v1_funct_1(E_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_8708,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_8614,c_8656])).

tff(c_8730,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_114,c_124,c_120,c_8708])).

tff(c_8732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8645,c_8730])).

tff(c_8733,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6866])).

tff(c_10416,plain,(
    ! [D_538,B_536,A_533,C_537,E_535,F_534] :
      ( k1_partfun1(A_533,B_536,C_537,D_538,E_535,F_534) = k5_relat_1(E_535,F_534)
      | ~ m1_subset_1(F_534,k1_zfmisc_1(k2_zfmisc_1(C_537,D_538)))
      | ~ v1_funct_1(F_534)
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_536)))
      | ~ v1_funct_1(E_535) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_10434,plain,(
    ! [A_533,B_536,E_535] :
      ( k1_partfun1(A_533,B_536,'#skF_1','#skF_1',E_535,'#skF_2') = k5_relat_1(E_535,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_535,k1_zfmisc_1(k2_zfmisc_1(A_533,B_536)))
      | ~ v1_funct_1(E_535) ) ),
    inference(resolution,[status(thm)],[c_120,c_10416])).

tff(c_10531,plain,(
    ! [A_542,B_543,E_544] :
      ( k1_partfun1(A_542,B_543,'#skF_1','#skF_1',E_544,'#skF_2') = k5_relat_1(E_544,'#skF_2')
      | ~ m1_subset_1(E_544,k1_zfmisc_1(k2_zfmisc_1(A_542,B_543)))
      | ~ v1_funct_1(E_544) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_10434])).

tff(c_10555,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_10531])).

tff(c_10578,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_8733,c_10555])).

tff(c_21257,plain,(
    ! [B_762,A_763] :
      ( k9_relat_1(k2_funct_1(B_762),k2_relat_1(k5_relat_1(A_763,B_762))) = k2_relat_1(A_763)
      | ~ r1_tarski(k2_relat_1(A_763),k1_relat_1(B_762))
      | ~ v2_funct_1(B_762)
      | ~ v1_funct_1(B_762)
      | ~ v1_relat_1(B_762)
      | ~ v1_relat_1(B_762)
      | ~ v1_relat_1(A_763) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_1330])).

tff(c_21326,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k1_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_10578,c_21257])).

tff(c_21397,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_226,c_226,c_124,c_110,c_6559,c_1595,c_21326])).

tff(c_21398,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_9677,c_21397])).

tff(c_21425,plain,(
    ~ v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_14111,c_21398])).

tff(c_21432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_21425])).

tff(c_21434,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_9672])).

tff(c_21444,plain,(
    k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21434,c_6346])).

tff(c_21445,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21434,c_654])).

tff(c_21723,plain,(
    ! [C_777,B_778,A_779] :
      ( m1_subset_1(k2_funct_1(C_777),k1_zfmisc_1(k2_zfmisc_1(B_778,A_779)))
      | k2_relset_1(A_779,B_778,C_777) != B_778
      | ~ v2_funct_1(C_777)
      | ~ m1_subset_1(C_777,k1_zfmisc_1(k2_zfmisc_1(A_779,B_778)))
      | ~ v1_funct_2(C_777,A_779,B_778)
      | ~ v1_funct_1(C_777) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_60,plain,(
    ! [C_37,A_35,B_36] :
      ( v4_relat_1(C_37,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_37265,plain,(
    ! [C_1062,B_1063,A_1064] :
      ( v4_relat_1(k2_funct_1(C_1062),B_1063)
      | k2_relset_1(A_1064,B_1063,C_1062) != B_1063
      | ~ v2_funct_1(C_1062)
      | ~ m1_subset_1(C_1062,k1_zfmisc_1(k2_zfmisc_1(A_1064,B_1063)))
      | ~ v1_funct_2(C_1062,A_1064,B_1063)
      | ~ v1_funct_1(C_1062) ) ),
    inference(resolution,[status(thm)],[c_21723,c_60])).

tff(c_37316,plain,
    ( v4_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_37265])).

tff(c_37360,plain,(
    v4_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_116,c_6271,c_21445,c_37316])).

tff(c_37366,plain,
    ( k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37360,c_24])).

tff(c_37369,plain,(
    k7_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8943,c_37366])).

tff(c_37442,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_37369,c_20])).

tff(c_37456,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8943,c_21444,c_37442])).

tff(c_88,plain,(
    ! [A_72] : k6_relat_1(A_72) = k6_partfun1(A_72) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_50,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_relat_1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_127,plain,(
    ! [A_30] :
      ( k5_relat_1(k2_funct_1(A_30),A_30) = k6_partfun1(k2_relat_1(A_30))
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_50])).

tff(c_44,plain,(
    ! [B_28,A_26] :
      ( k6_relat_1(k1_relat_1(B_28)) = B_28
      | k5_relat_1(A_26,B_28) != A_26
      | k2_relat_1(A_26) != k1_relat_1(B_28)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_8875,plain,(
    ! [B_481,A_482] :
      ( k6_partfun1(k1_relat_1(B_481)) = B_481
      | k5_relat_1(A_482,B_481) != A_482
      | k2_relat_1(A_482) != k1_relat_1(B_481)
      | ~ v1_funct_1(B_481)
      | ~ v1_relat_1(B_481)
      | ~ v1_funct_1(A_482)
      | ~ v1_relat_1(A_482) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_44])).

tff(c_45070,plain,(
    ! [A_1196] :
      ( k6_partfun1(k1_relat_1(A_1196)) = A_1196
      | k6_partfun1(k2_relat_1(A_1196)) != k2_funct_1(A_1196)
      | k2_relat_1(k2_funct_1(A_1196)) != k1_relat_1(A_1196)
      | ~ v1_funct_1(A_1196)
      | ~ v1_relat_1(A_1196)
      | ~ v1_funct_1(k2_funct_1(A_1196))
      | ~ v1_relat_1(k2_funct_1(A_1196))
      | ~ v2_funct_1(A_1196)
      | ~ v1_funct_1(A_1196)
      | ~ v1_relat_1(A_1196) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_8875])).

tff(c_45082,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k6_partfun1(k2_relat_1('#skF_3')) != k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_8943,c_45070])).

tff(c_45100,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_6271,c_9284,c_37456,c_6671,c_21434,c_6671,c_45082])).

tff(c_45109,plain,(
    k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_45100])).

tff(c_42,plain,(
    ! [A_23,B_25] :
      ( k9_relat_1(k2_funct_1(A_23),k9_relat_1(A_23,B_25)) = B_25
      | ~ r1_tarski(B_25,k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_6275,plain,
    ( k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1595,c_42])).

tff(c_6780,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_6275])).

tff(c_6783,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_6780])).

tff(c_6787,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_6783])).

tff(c_6789,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_6275])).

tff(c_6577,plain,
    ( v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6559,c_102])).

tff(c_6587,plain,(
    v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_6577])).

tff(c_6574,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2'))))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6559,c_100])).

tff(c_6585,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_6574])).

tff(c_6821,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_2'),'#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6585,c_66])).

tff(c_9260,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1',k2_relat_1('#skF_2'),'#skF_2') != k2_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6585,c_9257])).

tff(c_9281,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_6587,c_110,c_6821,c_9260])).

tff(c_21433,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_9672])).

tff(c_48,plain,(
    ! [A_29] :
      ( k1_relat_1(k2_funct_1(A_29)) = k2_relat_1(A_29)
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_678,plain,(
    ! [A_147] :
      ( m1_subset_1(A_147,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147),k2_relat_1(A_147))))
      | ~ v1_funct_1(A_147)
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_270])).

tff(c_704,plain,(
    ! [A_29] :
      ( m1_subset_1(k2_funct_1(A_29),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_29),k2_relat_1(k2_funct_1(A_29)))))
      | ~ v1_funct_1(k2_funct_1(A_29))
      | ~ v1_relat_1(k2_funct_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_678])).

tff(c_37571,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'),'#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_37456,c_704])).

tff(c_37652,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_6271,c_8943,c_9284,c_21434,c_37571])).

tff(c_106,plain,(
    ! [A_83,B_84] :
      ( k1_relset_1(A_83,A_83,B_84) = A_83
      | ~ m1_subset_1(B_84,k1_zfmisc_1(k2_zfmisc_1(A_83,A_83)))
      | ~ v1_funct_2(B_84,A_83,A_83)
      | ~ v1_funct_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_38363,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37652,c_106])).

tff(c_38452,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9284,c_21433,c_38363])).

tff(c_64,plain,(
    ! [A_42,B_43,C_44] :
      ( k1_relset_1(A_42,B_43,C_44) = k1_relat_1(C_44)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_172])).

tff(c_38456,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_37652,c_64])).

tff(c_41214,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38452,c_38456])).

tff(c_6788,plain,
    ( ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2')))
    | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')),'#skF_1') = k2_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6275])).

tff(c_9113,plain,(
    ~ r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6788])).

tff(c_9116,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_9113])).

tff(c_9122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_110,c_8,c_9116])).

tff(c_9124,plain,(
    r1_tarski(k2_relat_1('#skF_2'),k1_relat_1(k2_funct_1('#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_6788])).

tff(c_9136,plain,
    ( k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_9124,c_4])).

tff(c_35228,plain,(
    ~ r1_tarski(k1_relat_1(k2_funct_1('#skF_2')),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9136])).

tff(c_35231,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_35228])).

tff(c_35234,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_124,c_110,c_8,c_35231])).

tff(c_35235,plain,(
    k1_relat_1(k2_funct_1('#skF_2')) = k2_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_9136])).

tff(c_1248,plain,(
    ! [A_182] :
      ( v4_relat_1(A_182,k1_relat_1(A_182))
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_678,c_60])).

tff(c_1261,plain,(
    ! [A_182] :
      ( k7_relat_1(A_182,k1_relat_1(A_182)) = A_182
      | ~ v1_funct_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(resolution,[status(thm)],[c_1248,c_24])).

tff(c_35338,plain,
    ( k7_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = k2_funct_1('#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35235,c_1261])).

tff(c_35383,plain,(
    k7_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = k2_funct_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6789,c_9281,c_35338])).

tff(c_35670,plain,
    ( k9_relat_1(k2_funct_1('#skF_2'),k2_relat_1('#skF_2')) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_35383,c_20])).

tff(c_35684,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6789,c_1595,c_35670])).

tff(c_21521,plain,(
    ! [E_766,A_764,B_767,C_768,F_765,D_769] :
      ( k1_partfun1(A_764,B_767,C_768,D_769,E_766,F_765) = k5_relat_1(E_766,F_765)
      | ~ m1_subset_1(F_765,k1_zfmisc_1(k2_zfmisc_1(C_768,D_769)))
      | ~ v1_funct_1(F_765)
      | ~ m1_subset_1(E_766,k1_zfmisc_1(k2_zfmisc_1(A_764,B_767)))
      | ~ v1_funct_1(E_766) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_21535,plain,(
    ! [A_764,B_767,E_766] :
      ( k1_partfun1(A_764,B_767,'#skF_1','#skF_1',E_766,'#skF_2') = k5_relat_1(E_766,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_766,k1_zfmisc_1(k2_zfmisc_1(A_764,B_767)))
      | ~ v1_funct_1(E_766) ) ),
    inference(resolution,[status(thm)],[c_120,c_21521])).

tff(c_21829,plain,(
    ! [A_781,B_782,E_783] :
      ( k1_partfun1(A_781,B_782,'#skF_1','#skF_1',E_783,'#skF_2') = k5_relat_1(E_783,'#skF_2')
      | ~ m1_subset_1(E_783,k1_zfmisc_1(k2_zfmisc_1(A_781,B_782)))
      | ~ v1_funct_1(E_783) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_21535])).

tff(c_21850,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_114,c_21829])).

tff(c_21870,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_8733,c_21850])).

tff(c_8985,plain,(
    ! [B_485,A_486] :
      ( k5_relat_1(k2_funct_1(B_485),k2_funct_1(A_486)) = k2_funct_1(k5_relat_1(A_486,B_485))
      | ~ v2_funct_1(B_485)
      | ~ v2_funct_1(A_486)
      | ~ v1_funct_1(B_485)
      | ~ v1_relat_1(B_485)
      | ~ v1_funct_1(A_486)
      | ~ v1_relat_1(A_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_128,plain,(
    ! [B_28,A_26] :
      ( k6_partfun1(k1_relat_1(B_28)) = B_28
      | k5_relat_1(A_26,B_28) != A_26
      | k2_relat_1(A_26) != k1_relat_1(B_28)
      | ~ v1_funct_1(B_28)
      | ~ v1_relat_1(B_28)
      | ~ v1_funct_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_44])).

tff(c_54989,plain,(
    ! [A_1330,B_1331] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_1330))) = k2_funct_1(A_1330)
      | k2_funct_1(k5_relat_1(A_1330,B_1331)) != k2_funct_1(B_1331)
      | k2_relat_1(k2_funct_1(B_1331)) != k1_relat_1(k2_funct_1(A_1330))
      | ~ v1_funct_1(k2_funct_1(A_1330))
      | ~ v1_relat_1(k2_funct_1(A_1330))
      | ~ v1_funct_1(k2_funct_1(B_1331))
      | ~ v1_relat_1(k2_funct_1(B_1331))
      | ~ v2_funct_1(B_1331)
      | ~ v2_funct_1(A_1330)
      | ~ v1_funct_1(B_1331)
      | ~ v1_relat_1(B_1331)
      | ~ v1_funct_1(A_1330)
      | ~ v1_relat_1(A_1330) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8985,c_128])).

tff(c_55045,plain,
    ( k6_partfun1(k1_relat_1(k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_2')) != k1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_funct_1(k2_funct_1('#skF_2'))
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_21870,c_54989])).

tff(c_55132,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_118,c_226,c_124,c_6271,c_110,c_6789,c_9281,c_8943,c_9284,c_41214,c_35684,c_41214,c_55045])).

tff(c_55134,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_45109,c_55132])).

tff(c_55135,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_45100])).

tff(c_108,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_298])).

tff(c_55143,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55135,c_108])).

tff(c_55148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_55143])).

tff(c_55150,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_84,plain,(
    ! [A_65] : m1_subset_1(k6_partfun1(A_65),k1_zfmisc_1(k2_zfmisc_1(A_65,A_65))) ),
    inference(cnfTransformation,[status(thm)],[f_210])).

tff(c_55270,plain,(
    ! [A_1337] :
      ( v1_xboole_0(k6_partfun1(A_1337))
      | ~ v1_xboole_0(A_1337) ) ),
    inference(resolution,[status(thm)],[c_84,c_405])).

tff(c_178,plain,(
    ! [B_97,A_98] :
      ( ~ v1_xboole_0(B_97)
      | B_97 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_181,plain,(
    ! [A_98] :
      ( k1_xboole_0 = A_98
      | ~ v1_xboole_0(A_98) ) ),
    inference(resolution,[status(thm)],[c_2,c_178])).

tff(c_55163,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_55150,c_181])).

tff(c_55149,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_416])).

tff(c_55156,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_55149,c_181])).

tff(c_55181,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55163,c_55156])).

tff(c_55174,plain,(
    ! [A_98] :
      ( A_98 = '#skF_3'
      | ~ v1_xboole_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55156,c_181])).

tff(c_55258,plain,(
    ! [A_98] :
      ( A_98 = '#skF_1'
      | ~ v1_xboole_0(A_98) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55181,c_55174])).

tff(c_55308,plain,(
    ! [A_1339] :
      ( k6_partfun1(A_1339) = '#skF_1'
      | ~ v1_xboole_0(A_1339) ) ),
    inference(resolution,[status(thm)],[c_55270,c_55258])).

tff(c_55316,plain,(
    k6_partfun1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_55150,c_55308])).

tff(c_55209,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1',k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55181,c_108])).

tff(c_55376,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55316,c_55209])).

tff(c_417,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_120,c_405])).

tff(c_55166,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_55150,c_417])).

tff(c_55172,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_55166,c_181])).

tff(c_55186,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_55163,c_55172])).

tff(c_55194,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55186,c_120])).

tff(c_70,plain,(
    ! [A_52,B_53,D_55] :
      ( r2_relset_1(A_52,B_53,D_55,D_55)
      | ~ m1_subset_1(D_55,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_55480,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_55194,c_70])).

tff(c_55496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_55376,c_55480])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 22.88/14.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.23/14.22  
% 23.23/14.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.23/14.22  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k8_relset_1 > k7_relset_1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 23.23/14.22  
% 23.23/14.22  %Foreground sorts:
% 23.23/14.22  
% 23.23/14.22  
% 23.23/14.22  %Background operators:
% 23.23/14.22  
% 23.23/14.22  
% 23.23/14.22  %Foreground operators:
% 23.23/14.22  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 23.23/14.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 23.23/14.22  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 23.23/14.22  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 23.23/14.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 23.23/14.22  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 23.23/14.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 23.23/14.22  tff(k8_relset_1, type, k8_relset_1: ($i * $i * $i * $i) > $i).
% 23.23/14.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 23.23/14.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 23.23/14.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 23.23/14.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 23.23/14.22  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 23.23/14.22  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 23.23/14.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 23.23/14.22  tff('#skF_2', type, '#skF_2': $i).
% 23.23/14.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 23.23/14.22  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 23.23/14.22  tff('#skF_3', type, '#skF_3': $i).
% 23.23/14.22  tff('#skF_1', type, '#skF_1': $i).
% 23.23/14.22  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 23.23/14.22  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 23.23/14.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 23.23/14.22  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 23.23/14.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 23.23/14.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 23.23/14.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 23.23/14.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 23.23/14.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 23.23/14.22  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 23.23/14.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 23.23/14.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 23.23/14.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 23.23/14.22  
% 23.23/14.26  tff(f_298, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_funct_2)).
% 23.23/14.26  tff(f_188, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 23.23/14.26  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 23.23/14.26  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 23.23/14.26  tff(f_168, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 23.23/14.26  tff(f_161, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 23.23/14.26  tff(f_72, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 23.23/14.26  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 23.23/14.26  tff(f_103, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v2_funct_1(A) & r1_tarski(B, k1_relat_1(A))) => (k9_relat_1(k2_funct_1(A), k9_relat_1(A, B)) = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t177_funct_1)).
% 23.23/14.26  tff(f_220, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 23.23/14.26  tff(f_206, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 23.23/14.26  tff(f_244, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_funct_2)).
% 23.23/14.26  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 23.23/14.26  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 23.23/14.26  tff(f_172, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 23.23/14.26  tff(f_278, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_2)).
% 23.23/14.26  tff(f_270, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 23.23/14.26  tff(f_176, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 23.23/14.26  tff(f_260, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 23.23/14.26  tff(f_84, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 23.23/14.26  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 23.23/14.26  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 23.23/14.26  tff(f_222, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 23.23/14.26  tff(f_138, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 23.23/14.26  tff(f_118, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_funct_1)).
% 23.23/14.26  tff(f_128, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 23.23/14.26  tff(f_153, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 23.23/14.26  tff(f_210, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 23.23/14.26  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 23.23/14.26  tff(c_114, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_453, plain, (![A_137, B_138, D_139]: (r2_relset_1(A_137, B_138, D_139, D_139) | ~m1_subset_1(D_139, k1_zfmisc_1(k2_zfmisc_1(A_137, B_138))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 23.23/14.26  tff(c_461, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_114, c_453])).
% 23.23/14.26  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 23.23/14.26  tff(c_208, plain, (![B_105, A_106]: (v1_relat_1(B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_106)) | ~v1_relat_1(A_106))), inference(cnfTransformation, [status(thm)], [f_47])).
% 23.23/14.26  tff(c_214, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_114, c_208])).
% 23.23/14.26  tff(c_223, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_214])).
% 23.23/14.26  tff(c_118, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_405, plain, (![C_132, B_133, A_134]: (v1_xboole_0(C_132) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(B_133, A_134))) | ~v1_xboole_0(A_134))), inference(cnfTransformation, [status(thm)], [f_168])).
% 23.23/14.26  tff(c_416, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_114, c_405])).
% 23.23/14.26  tff(c_418, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_416])).
% 23.23/14.26  tff(c_308, plain, (![C_124, A_125, B_126]: (v4_relat_1(C_124, A_125) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 23.23/14.26  tff(c_319, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_114, c_308])).
% 23.23/14.26  tff(c_24, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 23.23/14.26  tff(c_323, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_319, c_24])).
% 23.23/14.26  tff(c_326, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_223, c_323])).
% 23.23/14.26  tff(c_20, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.23/14.26  tff(c_343, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_326, c_20])).
% 23.23/14.26  tff(c_347, plain, (k9_relat_1('#skF_3', '#skF_1')=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_343])).
% 23.23/14.26  tff(c_1330, plain, (![A_188, B_189]: (k9_relat_1(k2_funct_1(A_188), k9_relat_1(A_188, B_189))=B_189 | ~r1_tarski(B_189, k1_relat_1(A_188)) | ~v2_funct_1(A_188) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.23/14.26  tff(c_1366, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_347, c_1330])).
% 23.23/14.26  tff(c_1385, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_1366])).
% 23.23/14.26  tff(c_1600, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1385])).
% 23.23/14.26  tff(c_116, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_124, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_122, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_120, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_110, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_3414, plain, (![C_266, D_267, E_264, B_265, A_262, F_263]: (k1_partfun1(A_262, B_265, C_266, D_267, E_264, F_263)=k5_relat_1(E_264, F_263) | ~m1_subset_1(F_263, k1_zfmisc_1(k2_zfmisc_1(C_266, D_267))) | ~v1_funct_1(F_263) | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_265))) | ~v1_funct_1(E_264))), inference(cnfTransformation, [status(thm)], [f_220])).
% 23.23/14.26  tff(c_3430, plain, (![A_262, B_265, E_264]: (k1_partfun1(A_262, B_265, '#skF_1', '#skF_1', E_264, '#skF_2')=k5_relat_1(E_264, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_264, k1_zfmisc_1(k2_zfmisc_1(A_262, B_265))) | ~v1_funct_1(E_264))), inference(resolution, [status(thm)], [c_120, c_3414])).
% 23.23/14.26  tff(c_3663, plain, (![A_278, B_279, E_280]: (k1_partfun1(A_278, B_279, '#skF_1', '#skF_1', E_280, '#skF_2')=k5_relat_1(E_280, '#skF_2') | ~m1_subset_1(E_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))) | ~v1_funct_1(E_280))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_3430])).
% 23.23/14.26  tff(c_3687, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_3663])).
% 23.23/14.26  tff(c_3710, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_3687])).
% 23.23/14.26  tff(c_112, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_1889, plain, (![D_207, C_208, A_209, B_210]: (D_207=C_208 | ~r2_relset_1(A_209, B_210, C_208, D_207) | ~m1_subset_1(D_207, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~m1_subset_1(C_208, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 23.23/14.26  tff(c_1901, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_112, c_1889])).
% 23.23/14.26  tff(c_1924, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_1901])).
% 23.23/14.26  tff(c_1926, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1924])).
% 23.23/14.26  tff(c_3775, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3710, c_1926])).
% 23.23/14.26  tff(c_3786, plain, (![A_285, C_284, E_289, B_286, D_288, F_287]: (m1_subset_1(k1_partfun1(A_285, B_286, C_284, D_288, E_289, F_287), k1_zfmisc_1(k2_zfmisc_1(A_285, D_288))) | ~m1_subset_1(F_287, k1_zfmisc_1(k2_zfmisc_1(C_284, D_288))) | ~v1_funct_1(F_287) | ~m1_subset_1(E_289, k1_zfmisc_1(k2_zfmisc_1(A_285, B_286))) | ~v1_funct_1(E_289))), inference(cnfTransformation, [status(thm)], [f_206])).
% 23.23/14.26  tff(c_3838, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3710, c_3786])).
% 23.23/14.26  tff(c_3860, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_124, c_120, c_3838])).
% 23.23/14.26  tff(c_3861, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3775, c_3860])).
% 23.23/14.26  tff(c_3862, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_1924])).
% 23.23/14.26  tff(c_6192, plain, (![A_380, B_379, C_376, E_377, D_378]: (k1_xboole_0=C_376 | v2_funct_1(D_378) | ~v2_funct_1(k1_partfun1(A_380, B_379, B_379, C_376, D_378, E_377)) | ~m1_subset_1(E_377, k1_zfmisc_1(k2_zfmisc_1(B_379, C_376))) | ~v1_funct_2(E_377, B_379, C_376) | ~v1_funct_1(E_377) | ~m1_subset_1(D_378, k1_zfmisc_1(k2_zfmisc_1(A_380, B_379))) | ~v1_funct_2(D_378, A_380, B_379) | ~v1_funct_1(D_378))), inference(cnfTransformation, [status(thm)], [f_244])).
% 23.23/14.26  tff(c_6200, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3') | ~v2_funct_1('#skF_2') | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3862, c_6192])).
% 23.23/14.26  tff(c_6209, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_114, c_124, c_122, c_120, c_110, c_6200])).
% 23.23/14.26  tff(c_6210, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_1600, c_6209])).
% 23.23/14.26  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 23.23/14.26  tff(c_6267, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6210, c_2])).
% 23.23/14.26  tff(c_6269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_418, c_6267])).
% 23.23/14.26  tff(c_6271, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_1385])).
% 23.23/14.26  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.23/14.26  tff(c_739, plain, (![A_148, B_149, C_150]: (k1_relset_1(A_148, B_149, C_150)=k1_relat_1(C_150) | ~m1_subset_1(C_150, k1_zfmisc_1(k2_zfmisc_1(A_148, B_149))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 23.23/14.26  tff(c_755, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_739])).
% 23.23/14.26  tff(c_6639, plain, (![A_394, B_395]: (k1_relset_1(A_394, A_394, B_395)=A_394 | ~m1_subset_1(B_395, k1_zfmisc_1(k2_zfmisc_1(A_394, A_394))) | ~v1_funct_2(B_395, A_394, A_394) | ~v1_funct_1(B_395))), inference(cnfTransformation, [status(thm)], [f_278])).
% 23.23/14.26  tff(c_6648, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_6639])).
% 23.23/14.26  tff(c_6660, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_755, c_6648])).
% 23.23/14.26  tff(c_6315, plain, (![A_385, B_386]: (k1_relset_1(A_385, A_385, B_386)=A_385 | ~m1_subset_1(B_386, k1_zfmisc_1(k2_zfmisc_1(A_385, A_385))) | ~v1_funct_2(B_386, A_385, A_385) | ~v1_funct_1(B_386))), inference(cnfTransformation, [status(thm)], [f_278])).
% 23.23/14.26  tff(c_6324, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_6315])).
% 23.23/14.26  tff(c_6336, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_755, c_6324])).
% 23.23/14.26  tff(c_6270, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_1385])).
% 23.23/14.26  tff(c_6289, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6270])).
% 23.23/14.26  tff(c_6340, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6336, c_6289])).
% 23.23/14.26  tff(c_6345, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6340])).
% 23.23/14.26  tff(c_6347, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6270])).
% 23.23/14.26  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 23.23/14.26  tff(c_6350, plain, (k1_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_6347, c_4])).
% 23.23/14.26  tff(c_6598, plain, (~r1_tarski(k1_relat_1('#skF_3'), '#skF_1')), inference(splitLeft, [status(thm)], [c_6350])).
% 23.23/14.26  tff(c_6664, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6660, c_6598])).
% 23.23/14.26  tff(c_6670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6664])).
% 23.23/14.26  tff(c_6671, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_6350])).
% 23.23/14.26  tff(c_102, plain, (![A_82]: (v1_funct_2(A_82, k1_relat_1(A_82), k2_relat_1(A_82)) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_270])).
% 23.23/14.26  tff(c_6689, plain, (v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6671, c_102])).
% 23.23/14.26  tff(c_6699, plain, (v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_6689])).
% 23.23/14.26  tff(c_100, plain, (![A_82]: (m1_subset_1(A_82, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_82), k2_relat_1(A_82)))) | ~v1_funct_1(A_82) | ~v1_relat_1(A_82))), inference(cnfTransformation, [status(thm)], [f_270])).
% 23.23/14.26  tff(c_6686, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_6671, c_100])).
% 23.23/14.26  tff(c_6697, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_6686])).
% 23.23/14.26  tff(c_66, plain, (![A_45, B_46, C_47]: (k2_relset_1(A_45, B_46, C_47)=k2_relat_1(C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 23.23/14.26  tff(c_6741, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6697, c_66])).
% 23.23/14.26  tff(c_9257, plain, (![C_494, A_495, B_496]: (v1_funct_1(k2_funct_1(C_494)) | k2_relset_1(A_495, B_496, C_494)!=B_496 | ~v2_funct_1(C_494) | ~m1_subset_1(C_494, k1_zfmisc_1(k2_zfmisc_1(A_495, B_496))) | ~v1_funct_2(C_494, A_495, B_496) | ~v1_funct_1(C_494))), inference(cnfTransformation, [status(thm)], [f_260])).
% 23.23/14.26  tff(c_9263, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_6697, c_9257])).
% 23.23/14.26  tff(c_9284, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_6699, c_6271, c_6741, c_9263])).
% 23.23/14.26  tff(c_32, plain, (![A_20]: (v1_relat_1(k2_funct_1(A_20)) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_84])).
% 23.23/14.26  tff(c_22, plain, (![B_16, A_14]: (k9_relat_1(B_16, k2_relat_1(A_14))=k2_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_66])).
% 23.23/14.26  tff(c_6346, plain, (k9_relat_1(k2_funct_1('#skF_3'), k2_relat_1('#skF_3'))='#skF_1'), inference(splitRight, [status(thm)], [c_6270])).
% 23.23/14.26  tff(c_6361, plain, (k2_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_22, c_6346])).
% 23.23/14.26  tff(c_6367, plain, (k2_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_6361])).
% 23.23/14.26  tff(c_8933, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_6367])).
% 23.23/14.26  tff(c_8937, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_8933])).
% 23.23/14.26  tff(c_8941, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_8937])).
% 23.23/14.26  tff(c_8943, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_6367])).
% 23.23/14.26  tff(c_237, plain, (![C_111, B_112, A_113]: (v5_relat_1(C_111, B_112) | ~m1_subset_1(C_111, k1_zfmisc_1(k2_zfmisc_1(A_113, B_112))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 23.23/14.26  tff(c_248, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_114, c_237])).
% 23.23/14.26  tff(c_289, plain, (![B_120, A_121]: (k2_relat_1(k7_relat_1(B_120, A_121))=k9_relat_1(B_120, A_121) | ~v1_relat_1(B_120))), inference(cnfTransformation, [status(thm)], [f_59])).
% 23.23/14.26  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_53])).
% 23.23/14.26  tff(c_14040, plain, (![B_629, A_630, A_631]: (r1_tarski(k9_relat_1(B_629, A_630), A_631) | ~v5_relat_1(k7_relat_1(B_629, A_630), A_631) | ~v1_relat_1(k7_relat_1(B_629, A_630)) | ~v1_relat_1(B_629))), inference(superposition, [status(thm), theory('equality')], [c_289, c_16])).
% 23.23/14.26  tff(c_14082, plain, (![A_631]: (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), A_631) | ~v5_relat_1('#skF_3', A_631) | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_326, c_14040])).
% 23.23/14.26  tff(c_14111, plain, (![A_631]: (r1_tarski(k2_relat_1('#skF_3'), A_631) | ~v5_relat_1('#skF_3', A_631))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_223, c_326, c_347, c_14082])).
% 23.23/14.26  tff(c_642, plain, (![A_144, B_145, C_146]: (k2_relset_1(A_144, B_145, C_146)=k2_relat_1(C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_176])).
% 23.23/14.26  tff(c_654, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_642])).
% 23.23/14.26  tff(c_9629, plain, (![C_514, B_515, A_516]: (v1_funct_2(k2_funct_1(C_514), B_515, A_516) | k2_relset_1(A_516, B_515, C_514)!=B_515 | ~v2_funct_1(C_514) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_516, B_515))) | ~v1_funct_2(C_514, A_516, B_515) | ~v1_funct_1(C_514))), inference(cnfTransformation, [status(thm)], [f_260])).
% 23.23/14.26  tff(c_9650, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_9629])).
% 23.23/14.26  tff(c_9672, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_6271, c_654, c_9650])).
% 23.23/14.26  tff(c_9677, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_9672])).
% 23.23/14.26  tff(c_217, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_120, c_208])).
% 23.23/14.26  tff(c_226, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_217])).
% 23.23/14.26  tff(c_756, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_120, c_739])).
% 23.23/14.26  tff(c_6527, plain, (![A_392, B_393]: (k1_relset_1(A_392, A_392, B_393)=A_392 | ~m1_subset_1(B_393, k1_zfmisc_1(k2_zfmisc_1(A_392, A_392))) | ~v1_funct_2(B_393, A_392, A_392) | ~v1_funct_1(B_393))), inference(cnfTransformation, [status(thm)], [f_278])).
% 23.23/14.26  tff(c_6539, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_120, c_6527])).
% 23.23/14.26  tff(c_6551, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_756, c_6539])).
% 23.23/14.26  tff(c_1538, plain, (![A_200, B_201]: (k1_relset_1(A_200, A_200, B_201)=A_200 | ~m1_subset_1(B_201, k1_zfmisc_1(k2_zfmisc_1(A_200, A_200))) | ~v1_funct_2(B_201, A_200, A_200) | ~v1_funct_1(B_201))), inference(cnfTransformation, [status(thm)], [f_278])).
% 23.23/14.26  tff(c_1550, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_120, c_1538])).
% 23.23/14.26  tff(c_1562, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_124, c_122, c_756, c_1550])).
% 23.23/14.26  tff(c_320, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_120, c_308])).
% 23.23/14.26  tff(c_329, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_320, c_24])).
% 23.23/14.26  tff(c_332, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_226, c_329])).
% 23.23/14.26  tff(c_366, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_332, c_20])).
% 23.23/14.26  tff(c_370, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_366])).
% 23.23/14.26  tff(c_1363, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_370, c_1330])).
% 23.23/14.26  tff(c_1383, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_110, c_1363])).
% 23.23/14.26  tff(c_1444, plain, (~r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_1383])).
% 23.23/14.26  tff(c_1589, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1562, c_1444])).
% 23.23/14.26  tff(c_1594, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_1589])).
% 23.23/14.26  tff(c_1596, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_1383])).
% 23.23/14.26  tff(c_1599, plain, (k1_relat_1('#skF_2')='#skF_1' | ~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_1596, c_4])).
% 23.23/14.26  tff(c_6368, plain, (~r1_tarski(k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1599])).
% 23.23/14.26  tff(c_6552, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_6551, c_6368])).
% 23.23/14.26  tff(c_6558, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6552])).
% 23.23/14.26  tff(c_6559, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_1599])).
% 23.23/14.26  tff(c_1595, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_1383])).
% 23.23/14.26  tff(c_8486, plain, (![C_461, E_459, F_458, B_460, D_462, A_457]: (k1_partfun1(A_457, B_460, C_461, D_462, E_459, F_458)=k5_relat_1(E_459, F_458) | ~m1_subset_1(F_458, k1_zfmisc_1(k2_zfmisc_1(C_461, D_462))) | ~v1_funct_1(F_458) | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_460))) | ~v1_funct_1(E_459))), inference(cnfTransformation, [status(thm)], [f_220])).
% 23.23/14.26  tff(c_8504, plain, (![A_457, B_460, E_459]: (k1_partfun1(A_457, B_460, '#skF_1', '#skF_1', E_459, '#skF_2')=k5_relat_1(E_459, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_459, k1_zfmisc_1(k2_zfmisc_1(A_457, B_460))) | ~v1_funct_1(E_459))), inference(resolution, [status(thm)], [c_120, c_8486])).
% 23.23/14.26  tff(c_8567, plain, (![A_465, B_466, E_467]: (k1_partfun1(A_465, B_466, '#skF_1', '#skF_1', E_467, '#skF_2')=k5_relat_1(E_467, '#skF_2') | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(A_465, B_466))) | ~v1_funct_1(E_467))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_8504])).
% 23.23/14.26  tff(c_8591, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_8567])).
% 23.23/14.26  tff(c_8614, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_8591])).
% 23.23/14.26  tff(c_6831, plain, (![D_398, C_399, A_400, B_401]: (D_398=C_399 | ~r2_relset_1(A_400, B_401, C_399, D_398) | ~m1_subset_1(D_398, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 23.23/14.26  tff(c_6843, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_112, c_6831])).
% 23.23/14.26  tff(c_6866, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_6843])).
% 23.23/14.26  tff(c_6877, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_6866])).
% 23.23/14.26  tff(c_8645, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_8614, c_6877])).
% 23.23/14.26  tff(c_8656, plain, (![A_470, C_469, B_471, F_472, E_474, D_473]: (m1_subset_1(k1_partfun1(A_470, B_471, C_469, D_473, E_474, F_472), k1_zfmisc_1(k2_zfmisc_1(A_470, D_473))) | ~m1_subset_1(F_472, k1_zfmisc_1(k2_zfmisc_1(C_469, D_473))) | ~v1_funct_1(F_472) | ~m1_subset_1(E_474, k1_zfmisc_1(k2_zfmisc_1(A_470, B_471))) | ~v1_funct_1(E_474))), inference(cnfTransformation, [status(thm)], [f_206])).
% 23.23/14.26  tff(c_8708, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_8614, c_8656])).
% 23.23/14.26  tff(c_8730, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_118, c_114, c_124, c_120, c_8708])).
% 23.23/14.26  tff(c_8732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8645, c_8730])).
% 23.23/14.26  tff(c_8733, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_6866])).
% 23.23/14.26  tff(c_10416, plain, (![D_538, B_536, A_533, C_537, E_535, F_534]: (k1_partfun1(A_533, B_536, C_537, D_538, E_535, F_534)=k5_relat_1(E_535, F_534) | ~m1_subset_1(F_534, k1_zfmisc_1(k2_zfmisc_1(C_537, D_538))) | ~v1_funct_1(F_534) | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_536))) | ~v1_funct_1(E_535))), inference(cnfTransformation, [status(thm)], [f_220])).
% 23.23/14.26  tff(c_10434, plain, (![A_533, B_536, E_535]: (k1_partfun1(A_533, B_536, '#skF_1', '#skF_1', E_535, '#skF_2')=k5_relat_1(E_535, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_535, k1_zfmisc_1(k2_zfmisc_1(A_533, B_536))) | ~v1_funct_1(E_535))), inference(resolution, [status(thm)], [c_120, c_10416])).
% 23.23/14.26  tff(c_10531, plain, (![A_542, B_543, E_544]: (k1_partfun1(A_542, B_543, '#skF_1', '#skF_1', E_544, '#skF_2')=k5_relat_1(E_544, '#skF_2') | ~m1_subset_1(E_544, k1_zfmisc_1(k2_zfmisc_1(A_542, B_543))) | ~v1_funct_1(E_544))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_10434])).
% 23.23/14.26  tff(c_10555, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_10531])).
% 23.23/14.26  tff(c_10578, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_8733, c_10555])).
% 23.23/14.26  tff(c_21257, plain, (![B_762, A_763]: (k9_relat_1(k2_funct_1(B_762), k2_relat_1(k5_relat_1(A_763, B_762)))=k2_relat_1(A_763) | ~r1_tarski(k2_relat_1(A_763), k1_relat_1(B_762)) | ~v2_funct_1(B_762) | ~v1_funct_1(B_762) | ~v1_relat_1(B_762) | ~v1_relat_1(B_762) | ~v1_relat_1(A_763))), inference(superposition, [status(thm), theory('equality')], [c_22, c_1330])).
% 23.23/14.26  tff(c_21326, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k1_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_10578, c_21257])).
% 23.23/14.26  tff(c_21397, plain, (k2_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_226, c_226, c_124, c_110, c_6559, c_1595, c_21326])).
% 23.23/14.26  tff(c_21398, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_9677, c_21397])).
% 23.23/14.26  tff(c_21425, plain, (~v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_14111, c_21398])).
% 23.23/14.26  tff(c_21432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_21425])).
% 23.23/14.26  tff(c_21434, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_9672])).
% 23.23/14.26  tff(c_21444, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21434, c_6346])).
% 23.23/14.26  tff(c_21445, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_21434, c_654])).
% 23.23/14.26  tff(c_21723, plain, (![C_777, B_778, A_779]: (m1_subset_1(k2_funct_1(C_777), k1_zfmisc_1(k2_zfmisc_1(B_778, A_779))) | k2_relset_1(A_779, B_778, C_777)!=B_778 | ~v2_funct_1(C_777) | ~m1_subset_1(C_777, k1_zfmisc_1(k2_zfmisc_1(A_779, B_778))) | ~v1_funct_2(C_777, A_779, B_778) | ~v1_funct_1(C_777))), inference(cnfTransformation, [status(thm)], [f_260])).
% 23.23/14.26  tff(c_60, plain, (![C_37, A_35, B_36]: (v4_relat_1(C_37, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_161])).
% 23.23/14.26  tff(c_37265, plain, (![C_1062, B_1063, A_1064]: (v4_relat_1(k2_funct_1(C_1062), B_1063) | k2_relset_1(A_1064, B_1063, C_1062)!=B_1063 | ~v2_funct_1(C_1062) | ~m1_subset_1(C_1062, k1_zfmisc_1(k2_zfmisc_1(A_1064, B_1063))) | ~v1_funct_2(C_1062, A_1064, B_1063) | ~v1_funct_1(C_1062))), inference(resolution, [status(thm)], [c_21723, c_60])).
% 23.23/14.26  tff(c_37316, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_37265])).
% 23.23/14.26  tff(c_37360, plain, (v4_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_116, c_6271, c_21445, c_37316])).
% 23.23/14.26  tff(c_37366, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_37360, c_24])).
% 23.23/14.26  tff(c_37369, plain, (k7_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8943, c_37366])).
% 23.23/14.26  tff(c_37442, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_37369, c_20])).
% 23.23/14.26  tff(c_37456, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8943, c_21444, c_37442])).
% 23.23/14.26  tff(c_88, plain, (![A_72]: (k6_relat_1(A_72)=k6_partfun1(A_72))), inference(cnfTransformation, [status(thm)], [f_222])).
% 23.23/14.26  tff(c_50, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_relat_1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_138])).
% 23.23/14.26  tff(c_127, plain, (![A_30]: (k5_relat_1(k2_funct_1(A_30), A_30)=k6_partfun1(k2_relat_1(A_30)) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_50])).
% 23.23/14.26  tff(c_44, plain, (![B_28, A_26]: (k6_relat_1(k1_relat_1(B_28))=B_28 | k5_relat_1(A_26, B_28)!=A_26 | k2_relat_1(A_26)!=k1_relat_1(B_28) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_118])).
% 23.23/14.26  tff(c_8875, plain, (![B_481, A_482]: (k6_partfun1(k1_relat_1(B_481))=B_481 | k5_relat_1(A_482, B_481)!=A_482 | k2_relat_1(A_482)!=k1_relat_1(B_481) | ~v1_funct_1(B_481) | ~v1_relat_1(B_481) | ~v1_funct_1(A_482) | ~v1_relat_1(A_482))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_44])).
% 23.23/14.26  tff(c_45070, plain, (![A_1196]: (k6_partfun1(k1_relat_1(A_1196))=A_1196 | k6_partfun1(k2_relat_1(A_1196))!=k2_funct_1(A_1196) | k2_relat_1(k2_funct_1(A_1196))!=k1_relat_1(A_1196) | ~v1_funct_1(A_1196) | ~v1_relat_1(A_1196) | ~v1_funct_1(k2_funct_1(A_1196)) | ~v1_relat_1(k2_funct_1(A_1196)) | ~v2_funct_1(A_1196) | ~v1_funct_1(A_1196) | ~v1_relat_1(A_1196))), inference(superposition, [status(thm), theory('equality')], [c_127, c_8875])).
% 23.23/14.26  tff(c_45082, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k6_partfun1(k2_relat_1('#skF_3'))!=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_8943, c_45070])).
% 23.23/14.26  tff(c_45100, plain, (k6_partfun1('#skF_1')='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_6271, c_9284, c_37456, c_6671, c_21434, c_6671, c_45082])).
% 23.23/14.26  tff(c_45109, plain, (k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_45100])).
% 23.23/14.26  tff(c_42, plain, (![A_23, B_25]: (k9_relat_1(k2_funct_1(A_23), k9_relat_1(A_23, B_25))=B_25 | ~r1_tarski(B_25, k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_103])).
% 23.23/14.26  tff(c_6275, plain, (k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1595, c_42])).
% 23.23/14.26  tff(c_6780, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_6275])).
% 23.23/14.26  tff(c_6783, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_6780])).
% 23.23/14.26  tff(c_6787, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_6783])).
% 23.23/14.26  tff(c_6789, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_6275])).
% 23.23/14.26  tff(c_6577, plain, (v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6559, c_102])).
% 23.23/14.26  tff(c_6587, plain, (v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_6577])).
% 23.23/14.26  tff(c_6574, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2')))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6559, c_100])).
% 23.23/14.26  tff(c_6585, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_6574])).
% 23.23/14.26  tff(c_6821, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_2'), '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6585, c_66])).
% 23.23/14.26  tff(c_9260, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', k2_relat_1('#skF_2'), '#skF_2')!=k2_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_6585, c_9257])).
% 23.23/14.26  tff(c_9281, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_6587, c_110, c_6821, c_9260])).
% 23.23/14.26  tff(c_21433, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_9672])).
% 23.23/14.26  tff(c_48, plain, (![A_29]: (k1_relat_1(k2_funct_1(A_29))=k2_relat_1(A_29) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_128])).
% 23.23/14.26  tff(c_678, plain, (![A_147]: (m1_subset_1(A_147, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_147), k2_relat_1(A_147)))) | ~v1_funct_1(A_147) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_270])).
% 23.23/14.26  tff(c_704, plain, (![A_29]: (m1_subset_1(k2_funct_1(A_29), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(A_29), k2_relat_1(k2_funct_1(A_29))))) | ~v1_funct_1(k2_funct_1(A_29)) | ~v1_relat_1(k2_funct_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(superposition, [status(thm), theory('equality')], [c_48, c_678])).
% 23.23/14.26  tff(c_37571, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1(k2_relat_1('#skF_3'), '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_37456, c_704])).
% 23.23/14.26  tff(c_37652, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_6271, c_8943, c_9284, c_21434, c_37571])).
% 23.23/14.26  tff(c_106, plain, (![A_83, B_84]: (k1_relset_1(A_83, A_83, B_84)=A_83 | ~m1_subset_1(B_84, k1_zfmisc_1(k2_zfmisc_1(A_83, A_83))) | ~v1_funct_2(B_84, A_83, A_83) | ~v1_funct_1(B_84))), inference(cnfTransformation, [status(thm)], [f_278])).
% 23.23/14.26  tff(c_38363, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_37652, c_106])).
% 23.23/14.26  tff(c_38452, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_9284, c_21433, c_38363])).
% 23.23/14.26  tff(c_64, plain, (![A_42, B_43, C_44]: (k1_relset_1(A_42, B_43, C_44)=k1_relat_1(C_44) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_172])).
% 23.23/14.26  tff(c_38456, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_37652, c_64])).
% 23.23/14.26  tff(c_41214, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38452, c_38456])).
% 23.23/14.26  tff(c_6788, plain, (~v1_funct_1(k2_funct_1('#skF_2')) | ~v2_funct_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2'))) | k9_relat_1(k2_funct_1(k2_funct_1('#skF_2')), '#skF_1')=k2_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_6275])).
% 23.23/14.26  tff(c_9113, plain, (~r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitLeft, [status(thm)], [c_6788])).
% 23.23/14.26  tff(c_9116, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_9113])).
% 23.23/14.26  tff(c_9122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_110, c_8, c_9116])).
% 23.23/14.26  tff(c_9124, plain, (r1_tarski(k2_relat_1('#skF_2'), k1_relat_1(k2_funct_1('#skF_2')))), inference(splitRight, [status(thm)], [c_6788])).
% 23.23/14.26  tff(c_9136, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2') | ~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_9124, c_4])).
% 23.23/14.26  tff(c_35228, plain, (~r1_tarski(k1_relat_1(k2_funct_1('#skF_2')), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_9136])).
% 23.23/14.26  tff(c_35231, plain, (~r1_tarski(k2_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_48, c_35228])).
% 23.23/14.26  tff(c_35234, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_124, c_110, c_8, c_35231])).
% 23.23/14.26  tff(c_35235, plain, (k1_relat_1(k2_funct_1('#skF_2'))=k2_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_9136])).
% 23.23/14.26  tff(c_1248, plain, (![A_182]: (v4_relat_1(A_182, k1_relat_1(A_182)) | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_678, c_60])).
% 23.23/14.26  tff(c_1261, plain, (![A_182]: (k7_relat_1(A_182, k1_relat_1(A_182))=A_182 | ~v1_funct_1(A_182) | ~v1_relat_1(A_182))), inference(resolution, [status(thm)], [c_1248, c_24])).
% 23.23/14.26  tff(c_35338, plain, (k7_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))=k2_funct_1('#skF_2') | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_35235, c_1261])).
% 23.23/14.26  tff(c_35383, plain, (k7_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))=k2_funct_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6789, c_9281, c_35338])).
% 23.23/14.26  tff(c_35670, plain, (k9_relat_1(k2_funct_1('#skF_2'), k2_relat_1('#skF_2'))=k2_relat_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_35383, c_20])).
% 23.23/14.26  tff(c_35684, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6789, c_1595, c_35670])).
% 23.23/14.26  tff(c_21521, plain, (![E_766, A_764, B_767, C_768, F_765, D_769]: (k1_partfun1(A_764, B_767, C_768, D_769, E_766, F_765)=k5_relat_1(E_766, F_765) | ~m1_subset_1(F_765, k1_zfmisc_1(k2_zfmisc_1(C_768, D_769))) | ~v1_funct_1(F_765) | ~m1_subset_1(E_766, k1_zfmisc_1(k2_zfmisc_1(A_764, B_767))) | ~v1_funct_1(E_766))), inference(cnfTransformation, [status(thm)], [f_220])).
% 23.23/14.26  tff(c_21535, plain, (![A_764, B_767, E_766]: (k1_partfun1(A_764, B_767, '#skF_1', '#skF_1', E_766, '#skF_2')=k5_relat_1(E_766, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_766, k1_zfmisc_1(k2_zfmisc_1(A_764, B_767))) | ~v1_funct_1(E_766))), inference(resolution, [status(thm)], [c_120, c_21521])).
% 23.23/14.26  tff(c_21829, plain, (![A_781, B_782, E_783]: (k1_partfun1(A_781, B_782, '#skF_1', '#skF_1', E_783, '#skF_2')=k5_relat_1(E_783, '#skF_2') | ~m1_subset_1(E_783, k1_zfmisc_1(k2_zfmisc_1(A_781, B_782))) | ~v1_funct_1(E_783))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_21535])).
% 23.23/14.26  tff(c_21850, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_114, c_21829])).
% 23.23/14.26  tff(c_21870, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_118, c_8733, c_21850])).
% 23.23/14.26  tff(c_8985, plain, (![B_485, A_486]: (k5_relat_1(k2_funct_1(B_485), k2_funct_1(A_486))=k2_funct_1(k5_relat_1(A_486, B_485)) | ~v2_funct_1(B_485) | ~v2_funct_1(A_486) | ~v1_funct_1(B_485) | ~v1_relat_1(B_485) | ~v1_funct_1(A_486) | ~v1_relat_1(A_486))), inference(cnfTransformation, [status(thm)], [f_153])).
% 23.23/14.26  tff(c_128, plain, (![B_28, A_26]: (k6_partfun1(k1_relat_1(B_28))=B_28 | k5_relat_1(A_26, B_28)!=A_26 | k2_relat_1(A_26)!=k1_relat_1(B_28) | ~v1_funct_1(B_28) | ~v1_relat_1(B_28) | ~v1_funct_1(A_26) | ~v1_relat_1(A_26))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_44])).
% 23.23/14.26  tff(c_54989, plain, (![A_1330, B_1331]: (k6_partfun1(k1_relat_1(k2_funct_1(A_1330)))=k2_funct_1(A_1330) | k2_funct_1(k5_relat_1(A_1330, B_1331))!=k2_funct_1(B_1331) | k2_relat_1(k2_funct_1(B_1331))!=k1_relat_1(k2_funct_1(A_1330)) | ~v1_funct_1(k2_funct_1(A_1330)) | ~v1_relat_1(k2_funct_1(A_1330)) | ~v1_funct_1(k2_funct_1(B_1331)) | ~v1_relat_1(k2_funct_1(B_1331)) | ~v2_funct_1(B_1331) | ~v2_funct_1(A_1330) | ~v1_funct_1(B_1331) | ~v1_relat_1(B_1331) | ~v1_funct_1(A_1330) | ~v1_relat_1(A_1330))), inference(superposition, [status(thm), theory('equality')], [c_8985, c_128])).
% 23.23/14.26  tff(c_55045, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_21870, c_54989])).
% 23.23/14.26  tff(c_55132, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_118, c_226, c_124, c_6271, c_110, c_6789, c_9281, c_8943, c_9284, c_41214, c_35684, c_41214, c_55045])).
% 23.23/14.26  tff(c_55134, plain, $false, inference(negUnitSimplification, [status(thm)], [c_45109, c_55132])).
% 23.23/14.26  tff(c_55135, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_45100])).
% 23.23/14.26  tff(c_108, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_298])).
% 23.23/14.26  tff(c_55143, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_55135, c_108])).
% 23.23/14.26  tff(c_55148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_461, c_55143])).
% 23.23/14.26  tff(c_55150, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_416])).
% 23.23/14.26  tff(c_84, plain, (![A_65]: (m1_subset_1(k6_partfun1(A_65), k1_zfmisc_1(k2_zfmisc_1(A_65, A_65))))), inference(cnfTransformation, [status(thm)], [f_210])).
% 23.23/14.26  tff(c_55270, plain, (![A_1337]: (v1_xboole_0(k6_partfun1(A_1337)) | ~v1_xboole_0(A_1337))), inference(resolution, [status(thm)], [c_84, c_405])).
% 23.23/14.26  tff(c_178, plain, (![B_97, A_98]: (~v1_xboole_0(B_97) | B_97=A_98 | ~v1_xboole_0(A_98))), inference(cnfTransformation, [status(thm)], [f_40])).
% 23.23/14.26  tff(c_181, plain, (![A_98]: (k1_xboole_0=A_98 | ~v1_xboole_0(A_98))), inference(resolution, [status(thm)], [c_2, c_178])).
% 23.23/14.26  tff(c_55163, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_55150, c_181])).
% 23.23/14.26  tff(c_55149, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_416])).
% 23.23/14.26  tff(c_55156, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_55149, c_181])).
% 23.23/14.26  tff(c_55181, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_55163, c_55156])).
% 23.23/14.26  tff(c_55174, plain, (![A_98]: (A_98='#skF_3' | ~v1_xboole_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_55156, c_181])).
% 23.23/14.26  tff(c_55258, plain, (![A_98]: (A_98='#skF_1' | ~v1_xboole_0(A_98))), inference(demodulation, [status(thm), theory('equality')], [c_55181, c_55174])).
% 23.23/14.26  tff(c_55308, plain, (![A_1339]: (k6_partfun1(A_1339)='#skF_1' | ~v1_xboole_0(A_1339))), inference(resolution, [status(thm)], [c_55270, c_55258])).
% 23.23/14.26  tff(c_55316, plain, (k6_partfun1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_55150, c_55308])).
% 23.23/14.26  tff(c_55209, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_55181, c_108])).
% 23.23/14.26  tff(c_55376, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_55316, c_55209])).
% 23.23/14.26  tff(c_417, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_120, c_405])).
% 23.23/14.26  tff(c_55166, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_55150, c_417])).
% 23.23/14.26  tff(c_55172, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_55166, c_181])).
% 23.23/14.26  tff(c_55186, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_55163, c_55172])).
% 23.23/14.26  tff(c_55194, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_55186, c_120])).
% 23.23/14.26  tff(c_70, plain, (![A_52, B_53, D_55]: (r2_relset_1(A_52, B_53, D_55, D_55) | ~m1_subset_1(D_55, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))))), inference(cnfTransformation, [status(thm)], [f_188])).
% 23.23/14.26  tff(c_55480, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_55194, c_70])).
% 23.23/14.26  tff(c_55496, plain, $false, inference(negUnitSimplification, [status(thm)], [c_55376, c_55480])).
% 23.23/14.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 23.23/14.26  
% 23.23/14.26  Inference rules
% 23.23/14.26  ----------------------
% 23.23/14.26  #Ref     : 0
% 23.23/14.26  #Sup     : 13647
% 23.23/14.26  #Fact    : 0
% 23.23/14.26  #Define  : 0
% 23.23/14.26  #Split   : 56
% 23.23/14.26  #Chain   : 0
% 23.23/14.26  #Close   : 0
% 23.23/14.26  
% 23.23/14.26  Ordering : KBO
% 23.23/14.26  
% 23.23/14.26  Simplification rules
% 23.23/14.26  ----------------------
% 23.23/14.26  #Subsume      : 1449
% 23.23/14.26  #Demod        : 18949
% 23.23/14.26  #Tautology    : 3855
% 23.23/14.26  #SimpNegUnit  : 22
% 23.23/14.26  #BackRed      : 234
% 23.23/14.26  
% 23.23/14.26  #Partial instantiations: 0
% 23.23/14.26  #Strategies tried      : 1
% 23.23/14.26  
% 23.23/14.26  Timing (in seconds)
% 23.23/14.26  ----------------------
% 23.23/14.26  Preprocessing        : 0.40
% 23.23/14.26  Parsing              : 0.21
% 23.23/14.26  CNF conversion       : 0.03
% 23.23/14.26  Main loop            : 13.05
% 23.23/14.26  Inferencing          : 2.23
% 23.23/14.26  Reduction            : 7.09
% 23.23/14.26  Demodulation         : 6.19
% 23.23/14.26  BG Simplification    : 0.21
% 23.23/14.26  Subsumption          : 2.96
% 23.23/14.26  Abstraction          : 0.30
% 23.23/14.26  MUC search           : 0.00
% 23.23/14.26  Cooper               : 0.00
% 23.23/14.26  Total                : 13.54
% 23.23/14.26  Index Insertion      : 0.00
% 23.23/14.26  Index Deletion       : 0.00
% 23.23/14.26  Index Matching       : 0.00
% 23.23/14.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
