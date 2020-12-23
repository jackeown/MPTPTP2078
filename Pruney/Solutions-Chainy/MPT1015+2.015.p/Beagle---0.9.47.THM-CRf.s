%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:39 EST 2020

% Result     : Theorem 33.72s
% Output     : CNFRefutation 34.07s
% Verified   : 
% Statistics : Number of formulae       :  274 (19023 expanded)
%              Number of leaves         :   57 (6976 expanded)
%              Depth                    :   33
%              Number of atoms          :  663 (65728 expanded)
%              Number of equality atoms :  154 (7266 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_260,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_funct_2)).

tff(f_182,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_83,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_166,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_170,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_240,axiom,(
    ! [A,B] :
      ( ( v1_funct_1(B)
        & v1_funct_2(B,A,A)
        & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
     => k1_relset_1(A,A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_2)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_194,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_204,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & k2_relat_1(B) = k1_relat_1(A) )
           => ( v2_funct_1(B)
              & v2_funct_1(A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_206,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_145,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_174,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_222,axiom,(
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

tff(f_232,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_135,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_108,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(A) = k1_relat_1(B)
              & k5_relat_1(A,B) = A )
           => B = k6_relat_1(k1_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_funct_1)).

tff(f_160,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_94,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_476,plain,(
    ! [A_121,B_122,D_123] :
      ( r2_relset_1(A_121,B_122,D_123,D_123)
      | ~ m1_subset_1(D_123,k1_zfmisc_1(k2_zfmisc_1(A_121,B_122))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_485,plain,(
    r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_476])).

tff(c_18,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_169,plain,(
    ! [B_82,A_83] :
      ( v1_relat_1(B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_83))
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_175,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_94,c_169])).

tff(c_182,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_98,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_34,plain,(
    ! [A_21] :
      ( v1_relat_1(k2_funct_1(A_21))
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_248,plain,(
    ! [C_98,B_99,A_100] :
      ( v5_relat_1(C_98,B_99)
      | ~ m1_subset_1(C_98,k1_zfmisc_1(k2_zfmisc_1(A_100,B_99))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_260,plain,(
    v5_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_94,c_248])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k2_relat_1(B_9),A_8)
      | ~ v5_relat_1(B_9,A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_96,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_808,plain,(
    ! [A_158,B_159,C_160] :
      ( k1_relset_1(A_158,B_159,C_160) = k1_relat_1(C_160)
      | ~ m1_subset_1(C_160,k1_zfmisc_1(k2_zfmisc_1(A_158,B_159))) ) ),
    inference(cnfTransformation,[status(thm)],[f_170])).

tff(c_824,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_808])).

tff(c_1028,plain,(
    ! [A_189,B_190] :
      ( k1_relset_1(A_189,A_189,B_190) = A_189
      | ~ m1_subset_1(B_190,k1_zfmisc_1(k2_zfmisc_1(A_189,A_189)))
      | ~ v1_funct_2(B_190,A_189,A_189)
      | ~ v1_funct_1(B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_240])).

tff(c_1035,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_1028])).

tff(c_1042,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_824,c_1035])).

tff(c_36,plain,(
    ! [B_23,A_22] :
      ( k10_relat_1(B_23,k9_relat_1(B_23,A_22)) = A_22
      | ~ v2_funct_1(B_23)
      | ~ r1_tarski(A_22,k1_relat_1(B_23))
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1049,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_22)) = A_22
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_36])).

tff(c_1080,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_3',k9_relat_1('#skF_3',A_22)) = A_22
      | ~ v2_funct_1('#skF_3')
      | ~ r1_tarski(A_22,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_1049])).

tff(c_2596,plain,(
    ~ v2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_1080])).

tff(c_100,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_178,plain,
    ( v1_relat_1('#skF_2')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_100,c_169])).

tff(c_185,plain,(
    v1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_178])).

tff(c_104,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_90,plain,(
    v2_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_102,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_825,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_808])).

tff(c_1038,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_2') = '#skF_1'
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_100,c_1028])).

tff(c_1045,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_825,c_1038])).

tff(c_2498,plain,(
    ! [B_248,E_251,F_246,D_247,C_250,A_249] :
      ( m1_subset_1(k1_partfun1(A_249,B_248,C_250,D_247,E_251,F_246),k1_zfmisc_1(k2_zfmisc_1(A_249,D_247)))
      | ~ m1_subset_1(F_246,k1_zfmisc_1(k2_zfmisc_1(C_250,D_247)))
      | ~ v1_funct_1(F_246)
      | ~ m1_subset_1(E_251,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248)))
      | ~ v1_funct_1(E_251) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_92,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_1335,plain,(
    ! [D_195,C_196,A_197,B_198] :
      ( D_195 = C_196
      | ~ r2_relset_1(A_197,B_198,C_196,D_195)
      | ~ m1_subset_1(D_195,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198)))
      | ~ m1_subset_1(C_196,k1_zfmisc_1(k2_zfmisc_1(A_197,B_198))) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1351,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_92,c_1335])).

tff(c_1376,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2'
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_1351])).

tff(c_1380,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_1376])).

tff(c_2520,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_2')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2498,c_1380])).

tff(c_2555,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_94,c_104,c_100,c_2520])).

tff(c_2556,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1376])).

tff(c_3412,plain,(
    ! [B_289,E_285,D_290,A_287,C_286,F_288] :
      ( k1_partfun1(A_287,B_289,C_286,D_290,E_285,F_288) = k5_relat_1(E_285,F_288)
      | ~ m1_subset_1(F_288,k1_zfmisc_1(k2_zfmisc_1(C_286,D_290)))
      | ~ v1_funct_1(F_288)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_289)))
      | ~ v1_funct_1(E_285) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_3429,plain,(
    ! [A_287,B_289,E_285] :
      ( k1_partfun1(A_287,B_289,'#skF_1','#skF_1',E_285,'#skF_2') = k5_relat_1(E_285,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(A_287,B_289)))
      | ~ v1_funct_1(E_285) ) ),
    inference(resolution,[status(thm)],[c_100,c_3412])).

tff(c_3807,plain,(
    ! [A_300,B_301,E_302] :
      ( k1_partfun1(A_300,B_301,'#skF_1','#skF_1',E_302,'#skF_2') = k5_relat_1(E_302,'#skF_2')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301)))
      | ~ v1_funct_1(E_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_3429])).

tff(c_3841,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_3807])).

tff(c_3867,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2556,c_3841])).

tff(c_42,plain,(
    ! [B_29,A_27] :
      ( v2_funct_1(B_29)
      | k2_relat_1(B_29) != k1_relat_1(A_27)
      | ~ v2_funct_1(k5_relat_1(B_29,A_27))
      | ~ v1_funct_1(B_29)
      | ~ v1_relat_1(B_29)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_3879,plain,
    ( v2_funct_1('#skF_3')
    | k2_relat_1('#skF_3') != k1_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3867,c_42])).

tff(c_3890,plain,
    ( v2_funct_1('#skF_3')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_182,c_98,c_90,c_1045,c_3879])).

tff(c_3891,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2596,c_3890])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_217,plain,(
    ! [C_90,A_91,B_92] :
      ( v4_relat_1(C_90,A_91)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_91,B_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_230,plain,(
    v4_relat_1('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_100,c_217])).

tff(c_305,plain,(
    ! [B_108,A_109] :
      ( k7_relat_1(B_108,A_109) = B_108
      | ~ v4_relat_1(B_108,A_109)
      | ~ v1_relat_1(B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_311,plain,
    ( k7_relat_1('#skF_2','#skF_1') = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_230,c_305])).

tff(c_320,plain,(
    k7_relat_1('#skF_2','#skF_1') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_311])).

tff(c_341,plain,(
    ! [B_112,A_113] :
      ( k2_relat_1(k7_relat_1(B_112,A_113)) = k9_relat_1(B_112,A_113)
      | ~ v1_relat_1(B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_365,plain,
    ( k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_341])).

tff(c_373,plain,(
    k9_relat_1('#skF_2','#skF_1') = k2_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_365])).

tff(c_1103,plain,(
    ! [A_22] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_22)) = A_22
      | ~ v2_funct_1('#skF_2')
      | ~ r1_tarski(A_22,'#skF_1')
      | ~ v1_funct_1('#skF_2')
      | ~ v1_relat_1('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_36])).

tff(c_2564,plain,(
    ! [A_252] :
      ( k10_relat_1('#skF_2',k9_relat_1('#skF_2',A_252)) = A_252
      | ~ r1_tarski(A_252,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_90,c_1103])).

tff(c_2581,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_2564])).

tff(c_2589,plain,(
    k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2581])).

tff(c_22,plain,(
    ! [B_16,A_14] :
      ( k9_relat_1(B_16,k2_relat_1(A_14)) = k2_relat_1(k5_relat_1(A_14,B_16))
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2578,plain,(
    ! [A_14] :
      ( k10_relat_1('#skF_2',k2_relat_1(k5_relat_1(A_14,'#skF_2'))) = k2_relat_1(A_14)
      | ~ r1_tarski(k2_relat_1(A_14),'#skF_1')
      | ~ v1_relat_1('#skF_2')
      | ~ v1_relat_1(A_14) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2564])).

tff(c_2587,plain,(
    ! [A_14] :
      ( k10_relat_1('#skF_2',k2_relat_1(k5_relat_1(A_14,'#skF_2'))) = k2_relat_1(A_14)
      | ~ r1_tarski(k2_relat_1(A_14),'#skF_1')
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_2578])).

tff(c_3874,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_3867,c_2587])).

tff(c_3886,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2589,c_3874])).

tff(c_3989,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_3891,c_3886])).

tff(c_3992,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_3989])).

tff(c_3996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_260,c_3992])).

tff(c_3998,plain,(
    v2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1080])).

tff(c_72,plain,(
    ! [A_60] : k6_relat_1(A_60) = k6_partfun1(A_60) ),
    inference(cnfTransformation,[status(thm)],[f_206])).

tff(c_30,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_108,plain,(
    ! [A_20] : k2_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_30])).

tff(c_50,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_relat_1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_105,plain,(
    ! [A_31] :
      ( k5_relat_1(A_31,k2_funct_1(A_31)) = k6_partfun1(k1_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_50])).

tff(c_660,plain,(
    ! [A_145,B_146,C_147] :
      ( k2_relset_1(A_145,B_146,C_147) = k2_relat_1(C_147)
      | ~ m1_subset_1(C_147,k1_zfmisc_1(k2_zfmisc_1(A_145,B_146))) ) ),
    inference(cnfTransformation,[status(thm)],[f_174])).

tff(c_672,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_660])).

tff(c_4493,plain,(
    ! [C_321,B_322,A_323] :
      ( v1_funct_2(k2_funct_1(C_321),B_322,A_323)
      | k2_relset_1(A_323,B_322,C_321) != B_322
      | ~ v2_funct_1(C_321)
      | ~ m1_subset_1(C_321,k1_zfmisc_1(k2_zfmisc_1(A_323,B_322)))
      | ~ v1_funct_2(C_321,A_323,B_322)
      | ~ v1_funct_1(C_321) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4512,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_4493])).

tff(c_4527,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | k2_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_3998,c_672,c_4512])).

tff(c_4577,plain,(
    k2_relat_1('#skF_3') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4527])).

tff(c_4706,plain,(
    ! [C_334,F_336,D_338,E_333,B_337,A_335] :
      ( k1_partfun1(A_335,B_337,C_334,D_338,E_333,F_336) = k5_relat_1(E_333,F_336)
      | ~ m1_subset_1(F_336,k1_zfmisc_1(k2_zfmisc_1(C_334,D_338)))
      | ~ v1_funct_1(F_336)
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_335,B_337)))
      | ~ v1_funct_1(E_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_4721,plain,(
    ! [A_335,B_337,E_333] :
      ( k1_partfun1(A_335,B_337,'#skF_1','#skF_1',E_333,'#skF_2') = k5_relat_1(E_333,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_333,k1_zfmisc_1(k2_zfmisc_1(A_335,B_337)))
      | ~ v1_funct_1(E_333) ) ),
    inference(resolution,[status(thm)],[c_100,c_4706])).

tff(c_5173,plain,(
    ! [A_356,B_357,E_358] :
      ( k1_partfun1(A_356,B_357,'#skF_1','#skF_1',E_358,'#skF_2') = k5_relat_1(E_358,'#skF_2')
      | ~ m1_subset_1(E_358,k1_zfmisc_1(k2_zfmisc_1(A_356,B_357)))
      | ~ v1_funct_1(E_358) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_4721])).

tff(c_5201,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_5173])).

tff(c_5221,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2556,c_5201])).

tff(c_5228,plain,
    ( k10_relat_1('#skF_2',k2_relat_1('#skF_2')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5221,c_2587])).

tff(c_5240,plain,
    ( k2_relat_1('#skF_3') = '#skF_1'
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_2589,c_5228])).

tff(c_5241,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_4577,c_5240])).

tff(c_5251,plain,
    ( ~ v5_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_5241])).

tff(c_5255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_260,c_5251])).

tff(c_5257,plain,(
    k2_relat_1('#skF_3') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4527])).

tff(c_5291,plain,(
    ! [B_16] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_16)) = k9_relat_1(B_16,'#skF_1')
      | ~ v1_relat_1(B_16)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5257,c_22])).

tff(c_5704,plain,(
    ! [B_386] :
      ( k2_relat_1(k5_relat_1('#skF_3',B_386)) = k9_relat_1(B_386,'#skF_1')
      | ~ v1_relat_1(B_386) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_5291])).

tff(c_5758,plain,
    ( k2_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) = k9_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_5704])).

tff(c_5768,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_1') = '#skF_1'
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_108,c_1042,c_5758])).

tff(c_5769,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5768])).

tff(c_5838,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_5769])).

tff(c_5842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_5838])).

tff(c_5844,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5768])).

tff(c_82,plain,(
    ! [A_64] :
      ( v1_funct_2(A_64,k1_relat_1(A_64),k2_relat_1(A_64))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_1067,plain,
    ( v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_82])).

tff(c_1092,plain,(
    v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_1067])).

tff(c_26,plain,(
    ! [A_19] :
      ( r1_tarski(A_19,k2_zfmisc_1(k1_relat_1(A_19),k2_relat_1(A_19)))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1076,plain,
    ( r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3')))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_26])).

tff(c_1098,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_1076])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_671,plain,(
    ! [A_145,B_146,A_3] :
      ( k2_relset_1(A_145,B_146,A_3) = k2_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_145,B_146)) ) ),
    inference(resolution,[status(thm)],[c_10,c_660])).

tff(c_1225,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1098,c_671])).

tff(c_80,plain,(
    ! [A_64] :
      ( m1_subset_1(A_64,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_64),k2_relat_1(A_64))))
      | ~ v1_funct_1(A_64)
      | ~ v1_relat_1(A_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_232])).

tff(c_1058,plain,
    ( m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3'))))
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_80])).

tff(c_1086,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_1058])).

tff(c_4389,plain,(
    ! [C_318,A_319,B_320] :
      ( v1_funct_1(k2_funct_1(C_318))
      | k2_relset_1(A_319,B_320,C_318) != B_320
      | ~ v2_funct_1(C_318)
      | ~ m1_subset_1(C_318,k1_zfmisc_1(k2_zfmisc_1(A_319,B_320)))
      | ~ v1_funct_2(C_318,A_319,B_320)
      | ~ v1_funct_1(C_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_4395,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1',k2_relat_1('#skF_3'),'#skF_3') != k2_relat_1('#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1',k2_relat_1('#skF_3'))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1086,c_4389])).

tff(c_4415,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_1092,c_3998,c_1225,c_4395])).

tff(c_44,plain,(
    ! [A_30] :
      ( k2_relat_1(k2_funct_1(A_30)) = k1_relat_1(A_30)
      | ~ v2_funct_1(A_30)
      | ~ v1_funct_1(A_30)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_513,plain,(
    ! [A_130] :
      ( k1_relat_1(k2_funct_1(A_130)) = k2_relat_1(A_130)
      | ~ v2_funct_1(A_130)
      | ~ v1_funct_1(A_130)
      | ~ v1_relat_1(A_130) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_47030,plain,(
    ! [A_1226] :
      ( r1_tarski(k2_funct_1(A_1226),k2_zfmisc_1(k2_relat_1(A_1226),k2_relat_1(k2_funct_1(A_1226))))
      | ~ v1_relat_1(k2_funct_1(A_1226))
      | ~ v2_funct_1(A_1226)
      | ~ v1_funct_1(A_1226)
      | ~ v1_relat_1(A_1226) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_513,c_26])).

tff(c_47064,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5257,c_47030])).

tff(c_47101,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_5844,c_47064])).

tff(c_259,plain,(
    ! [A_3,B_99,A_100] :
      ( v5_relat_1(A_3,B_99)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_100,B_99)) ) ),
    inference(resolution,[status(thm)],[c_10,c_248])).

tff(c_47143,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_47101,c_259])).

tff(c_47164,plain,
    ( v5_relat_1(k2_funct_1('#skF_3'),k1_relat_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_47143])).

tff(c_47172,plain,(
    v5_relat_1(k2_funct_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_1042,c_47164])).

tff(c_573,plain,(
    ! [A_137] :
      ( k2_relat_1(k2_funct_1(A_137)) = k1_relat_1(A_137)
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_588,plain,(
    ! [A_137,A_8] :
      ( r1_tarski(k1_relat_1(A_137),A_8)
      | ~ v5_relat_1(k2_funct_1(A_137),A_8)
      | ~ v1_relat_1(k2_funct_1(A_137))
      | ~ v2_funct_1(A_137)
      | ~ v1_funct_1(A_137)
      | ~ v1_relat_1(A_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_573,c_16])).

tff(c_47159,plain,
    ( r1_tarski(k1_relat_1('#skF_3'),k2_relat_1(k2_funct_1('#skF_3')))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_47143,c_588])).

tff(c_47167,plain,(
    r1_tarski('#skF_1',k2_relat_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_5844,c_1042,c_47159])).

tff(c_262,plain,(
    ! [B_101,A_102] :
      ( r1_tarski(k2_relat_1(B_101),A_102)
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_281,plain,(
    ! [B_101,A_102] :
      ( k2_relat_1(B_101) = A_102
      | ~ r1_tarski(A_102,k2_relat_1(B_101))
      | ~ v5_relat_1(B_101,A_102)
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_47276,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v5_relat_1(k2_funct_1('#skF_3'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_47167,c_281])).

tff(c_47288,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_47172,c_47276])).

tff(c_48,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_relat_1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_106,plain,(
    ! [A_31] :
      ( k5_relat_1(k2_funct_1(A_31),A_31) = k6_partfun1(k2_relat_1(A_31))
      | ~ v2_funct_1(A_31)
      | ~ v1_funct_1(A_31)
      | ~ v1_relat_1(A_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_48])).

tff(c_5256,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4527])).

tff(c_47133,plain,
    ( r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_1',k1_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_47101])).

tff(c_47150,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_1042,c_47133])).

tff(c_1039,plain,(
    ! [A_189,A_3] :
      ( k1_relset_1(A_189,A_189,A_3) = A_189
      | ~ v1_funct_2(A_3,A_189,A_189)
      | ~ v1_funct_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_189,A_189)) ) ),
    inference(resolution,[status(thm)],[c_10,c_1028])).

tff(c_47605,plain,
    ( k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1'
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_47150,c_1039])).

tff(c_47636,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4415,c_5256,c_47605])).

tff(c_823,plain,(
    ! [A_158,B_159,A_3] :
      ( k1_relset_1(A_158,B_159,A_3) = k1_relat_1(A_3)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_158,B_159)) ) ),
    inference(resolution,[status(thm)],[c_10,c_808])).

tff(c_47637,plain,(
    k1_relset_1('#skF_1','#skF_1',k2_funct_1('#skF_3')) = k1_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_47150,c_823])).

tff(c_47980,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_47636,c_47637])).

tff(c_48022,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1(k2_funct_1('#skF_3')))))
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_47980,c_80])).

tff(c_48072,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_4415,c_47288,c_48022])).

tff(c_5268,plain,(
    k2_relset_1('#skF_1','#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5257,c_672])).

tff(c_74,plain,(
    ! [C_63,B_62,A_61] :
      ( m1_subset_1(k2_funct_1(C_63),k1_zfmisc_1(k2_zfmisc_1(B_62,A_61)))
      | k2_relset_1(A_61,B_62,C_63) != B_62
      | ~ v2_funct_1(C_63)
      | ~ m1_subset_1(C_63,k1_zfmisc_1(k2_zfmisc_1(A_61,B_62)))
      | ~ v1_funct_2(C_63,A_61,B_62)
      | ~ v1_funct_1(C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_5451,plain,(
    ! [E_370,B_374,C_371,A_372,F_373,D_375] :
      ( k1_partfun1(A_372,B_374,C_371,D_375,E_370,F_373) = k5_relat_1(E_370,F_373)
      | ~ m1_subset_1(F_373,k1_zfmisc_1(k2_zfmisc_1(C_371,D_375)))
      | ~ v1_funct_1(F_373)
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_372,B_374)))
      | ~ v1_funct_1(E_370) ) ),
    inference(cnfTransformation,[status(thm)],[f_204])).

tff(c_5462,plain,(
    ! [A_372,B_374,E_370] :
      ( k1_partfun1(A_372,B_374,'#skF_1','#skF_1',E_370,'#skF_3') = k5_relat_1(E_370,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_372,B_374)))
      | ~ v1_funct_1(E_370) ) ),
    inference(resolution,[status(thm)],[c_94,c_5451])).

tff(c_6038,plain,(
    ! [A_400,B_401,E_402] :
      ( k1_partfun1(A_400,B_401,'#skF_1','#skF_1',E_402,'#skF_3') = k5_relat_1(E_402,'#skF_3')
      | ~ m1_subset_1(E_402,k1_zfmisc_1(k2_zfmisc_1(A_400,B_401)))
      | ~ v1_funct_1(E_402) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_5462])).

tff(c_61652,plain,(
    ! [B_1501,A_1502,C_1503] :
      ( k1_partfun1(B_1501,A_1502,'#skF_1','#skF_1',k2_funct_1(C_1503),'#skF_3') = k5_relat_1(k2_funct_1(C_1503),'#skF_3')
      | ~ v1_funct_1(k2_funct_1(C_1503))
      | k2_relset_1(A_1502,B_1501,C_1503) != B_1501
      | ~ v2_funct_1(C_1503)
      | ~ m1_subset_1(C_1503,k1_zfmisc_1(k2_zfmisc_1(A_1502,B_1501)))
      | ~ v1_funct_2(C_1503,A_1502,B_1501)
      | ~ v1_funct_1(C_1503) ) ),
    inference(resolution,[status(thm)],[c_74,c_6038])).

tff(c_61686,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | k2_relset_1('#skF_1','#skF_1','#skF_3') != '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_61652])).

tff(c_61712,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1',k2_funct_1('#skF_3'),'#skF_3') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_96,c_3998,c_5268,c_4415,c_61686])).

tff(c_66,plain,(
    ! [B_49,F_53,A_48,D_51,E_52,C_50] :
      ( m1_subset_1(k1_partfun1(A_48,B_49,C_50,D_51,E_52,F_53),k1_zfmisc_1(k2_zfmisc_1(A_48,D_51)))
      | ~ m1_subset_1(F_53,k1_zfmisc_1(k2_zfmisc_1(C_50,D_51)))
      | ~ v1_funct_1(F_53)
      | ~ m1_subset_1(E_52,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49)))
      | ~ v1_funct_1(E_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_61897,plain,
    ( m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_61712,c_66])).

tff(c_61901,plain,(
    m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4415,c_48072,c_98,c_94,c_61897])).

tff(c_12,plain,(
    ! [B_7,A_5] :
      ( v1_relat_1(B_7)
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_5))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_61967,plain,
    ( v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(resolution,[status(thm)],[c_61901,c_12])).

tff(c_62017,plain,(
    v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_61967])).

tff(c_62023,plain,
    ( v1_relat_1(k6_partfun1(k2_relat_1('#skF_3')))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_62017])).

tff(c_62025,plain,(
    v1_relat_1(k6_partfun1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_5257,c_62023])).

tff(c_28,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_109,plain,(
    ! [A_20] : k1_relat_1(k6_partfun1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_28])).

tff(c_382,plain,(
    ! [A_114] :
      ( r1_tarski(A_114,k2_zfmisc_1(k1_relat_1(A_114),k2_relat_1(A_114)))
      | ~ v1_relat_1(A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_228,plain,(
    ! [A_3,A_91,B_92] :
      ( v4_relat_1(A_3,A_91)
      | ~ r1_tarski(A_3,k2_zfmisc_1(A_91,B_92)) ) ),
    inference(resolution,[status(thm)],[c_10,c_217])).

tff(c_417,plain,(
    ! [A_115] :
      ( v4_relat_1(A_115,k1_relat_1(A_115))
      | ~ v1_relat_1(A_115) ) ),
    inference(resolution,[status(thm)],[c_382,c_228])).

tff(c_440,plain,(
    ! [A_117] :
      ( v4_relat_1(k6_partfun1(A_117),A_117)
      | ~ v1_relat_1(k6_partfun1(A_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_417])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k7_relat_1(B_18,A_17) = B_18
      | ~ v4_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_444,plain,(
    ! [A_117] :
      ( k7_relat_1(k6_partfun1(A_117),A_117) = k6_partfun1(A_117)
      | ~ v1_relat_1(k6_partfun1(A_117)) ) ),
    inference(resolution,[status(thm)],[c_440,c_24])).

tff(c_62164,plain,(
    k7_relat_1(k6_partfun1('#skF_1'),'#skF_1') = k6_partfun1('#skF_1') ),
    inference(resolution,[status(thm)],[c_62025,c_444])).

tff(c_56,plain,(
    ! [C_37,A_35,B_36] :
      ( v4_relat_1(C_37,A_35)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_62014,plain,(
    v4_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_61901,c_56])).

tff(c_62280,plain,
    ( k7_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),'#skF_1') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_62014,c_24])).

tff(c_62286,plain,(
    k7_relat_1(k5_relat_1(k2_funct_1('#skF_3'),'#skF_3'),'#skF_1') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62017,c_62280])).

tff(c_76461,plain,
    ( k7_relat_1(k6_partfun1(k2_relat_1('#skF_3')),'#skF_1') = k5_relat_1(k2_funct_1('#skF_3'),'#skF_3')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_62286])).

tff(c_76481,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_3998,c_62164,c_5257,c_76461])).

tff(c_38,plain,(
    ! [B_26,A_24] :
      ( k6_relat_1(k1_relat_1(B_26)) = B_26
      | k5_relat_1(A_24,B_26) != A_24
      | k2_relat_1(A_24) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_107,plain,(
    ! [B_26,A_24] :
      ( k6_partfun1(k1_relat_1(B_26)) = B_26
      | k5_relat_1(A_24,B_26) != A_24
      | k2_relat_1(A_24) != k1_relat_1(B_26)
      | ~ v1_funct_1(B_26)
      | ~ v1_relat_1(B_26)
      | ~ v1_funct_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_38])).

tff(c_76508,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3')
    | k2_relat_1(k2_funct_1('#skF_3')) != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3')
    | ~ v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_76481,c_107])).

tff(c_76530,plain,
    ( k6_partfun1('#skF_1') = '#skF_3'
    | k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5844,c_4415,c_182,c_98,c_1042,c_47288,c_1042,c_76508])).

tff(c_76654,plain,(
    k6_partfun1('#skF_1') != k2_funct_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_76530])).

tff(c_4120,plain,(
    ! [A_311] :
      ( k10_relat_1('#skF_2',k2_relat_1(k5_relat_1(A_311,'#skF_2'))) = k2_relat_1(A_311)
      | ~ r1_tarski(k2_relat_1(A_311),'#skF_1')
      | ~ v1_relat_1(A_311) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_2578])).

tff(c_4134,plain,
    ( k10_relat_1('#skF_2',k2_relat_1(k6_partfun1(k2_relat_1('#skF_2')))) = k2_relat_1(k2_funct_1('#skF_2'))
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2'))
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_4120])).

tff(c_4140,plain,
    ( k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1'
    | ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_90,c_2589,c_108,c_4134])).

tff(c_4141,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_4140])).

tff(c_4144,plain,
    ( ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_4141])).

tff(c_4148,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_4144])).

tff(c_4150,plain,(
    v1_relat_1(k2_funct_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_4140])).

tff(c_1121,plain,
    ( v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_82])).

tff(c_1146,plain,(
    v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_1121])).

tff(c_1130,plain,
    ( r1_tarski('#skF_2',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_26])).

tff(c_1152,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_1130])).

tff(c_1190,plain,(
    k2_relset_1('#skF_1',k2_relat_1('#skF_2'),'#skF_2') = k2_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1152,c_671])).

tff(c_1112,plain,
    ( m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2'))))
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1045,c_80])).

tff(c_1140,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_1112])).

tff(c_4398,plain,
    ( v1_funct_1(k2_funct_1('#skF_2'))
    | k2_relset_1('#skF_1',k2_relat_1('#skF_2'),'#skF_2') != k2_relat_1('#skF_2')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1',k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1140,c_4389])).

tff(c_4418,plain,(
    v1_funct_1(k2_funct_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1146,c_90,c_1190,c_4398])).

tff(c_4149,plain,
    ( ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1')
    | k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4140])).

tff(c_4151,plain,(
    ~ r1_tarski(k2_relat_1(k2_funct_1('#skF_2')),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4149])).

tff(c_4154,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_2'),'#skF_1')
    | ~ v2_funct_1('#skF_2')
    | ~ v1_funct_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_4151])).

tff(c_4160,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_104,c_90,c_6,c_1045,c_4154])).

tff(c_4161,plain,(
    k2_relat_1(k2_funct_1('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4149])).

tff(c_5464,plain,(
    ! [A_372,B_374,E_370] :
      ( k1_partfun1(A_372,B_374,'#skF_1','#skF_1',E_370,'#skF_2') = k5_relat_1(E_370,'#skF_2')
      | ~ v1_funct_1('#skF_2')
      | ~ m1_subset_1(E_370,k1_zfmisc_1(k2_zfmisc_1(A_372,B_374)))
      | ~ v1_funct_1(E_370) ) ),
    inference(resolution,[status(thm)],[c_100,c_5451])).

tff(c_5644,plain,(
    ! [A_383,B_384,E_385] :
      ( k1_partfun1(A_383,B_384,'#skF_1','#skF_1',E_385,'#skF_2') = k5_relat_1(E_385,'#skF_2')
      | ~ m1_subset_1(E_385,k1_zfmisc_1(k2_zfmisc_1(A_383,B_384)))
      | ~ v1_funct_1(E_385) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_5464])).

tff(c_5663,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_3','#skF_2') = k5_relat_1('#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_94,c_5644])).

tff(c_5676,plain,(
    k5_relat_1('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_2556,c_5663])).

tff(c_4163,plain,(
    ! [B_312,A_313] :
      ( k5_relat_1(k2_funct_1(B_312),k2_funct_1(A_313)) = k2_funct_1(k5_relat_1(A_313,B_312))
      | ~ v2_funct_1(B_312)
      | ~ v2_funct_1(A_313)
      | ~ v1_funct_1(B_312)
      | ~ v1_relat_1(B_312)
      | ~ v1_funct_1(A_313)
      | ~ v1_relat_1(A_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_160])).

tff(c_92587,plain,(
    ! [A_2070,B_2071] :
      ( k6_partfun1(k1_relat_1(k2_funct_1(A_2070))) = k2_funct_1(A_2070)
      | k2_funct_1(k5_relat_1(A_2070,B_2071)) != k2_funct_1(B_2071)
      | k2_relat_1(k2_funct_1(B_2071)) != k1_relat_1(k2_funct_1(A_2070))
      | ~ v1_funct_1(k2_funct_1(A_2070))
      | ~ v1_relat_1(k2_funct_1(A_2070))
      | ~ v1_funct_1(k2_funct_1(B_2071))
      | ~ v1_relat_1(k2_funct_1(B_2071))
      | ~ v2_funct_1(B_2071)
      | ~ v2_funct_1(A_2070)
      | ~ v1_funct_1(B_2071)
      | ~ v1_relat_1(B_2071)
      | ~ v1_funct_1(A_2070)
      | ~ v1_relat_1(A_2070) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4163,c_107])).

tff(c_92603,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_5676,c_92587])).

tff(c_92626,plain,(
    k6_partfun1('#skF_1') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_98,c_185,c_104,c_3998,c_90,c_4150,c_4418,c_5844,c_4415,c_4161,c_47980,c_47980,c_92603])).

tff(c_92628,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76654,c_92626])).

tff(c_92629,plain,(
    k6_partfun1('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_76530])).

tff(c_88,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3',k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_92650,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92629,c_88])).

tff(c_92669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_92650])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:27:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 33.72/23.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.79/24.01  
% 33.79/24.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 33.79/24.01  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 33.79/24.01  
% 33.79/24.01  %Foreground sorts:
% 33.79/24.01  
% 33.79/24.01  
% 33.79/24.01  %Background operators:
% 33.79/24.01  
% 33.79/24.01  
% 33.79/24.01  %Foreground operators:
% 33.79/24.01  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 33.79/24.01  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 33.79/24.01  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 33.79/24.01  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 33.79/24.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 33.79/24.01  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 33.79/24.01  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 33.79/24.01  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 33.79/24.01  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 33.79/24.01  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 33.79/24.01  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 33.79/24.01  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 33.79/24.01  tff('#skF_2', type, '#skF_2': $i).
% 33.79/24.01  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 33.79/24.01  tff('#skF_3', type, '#skF_3': $i).
% 33.79/24.01  tff('#skF_1', type, '#skF_1': $i).
% 33.79/24.01  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 33.79/24.01  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 33.79/24.01  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 33.79/24.01  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 33.79/24.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 33.79/24.01  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 33.79/24.01  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 33.79/24.01  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 33.79/24.01  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 33.79/24.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 33.79/24.01  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 33.79/24.01  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 33.79/24.01  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 33.79/24.01  
% 34.07/24.05  tff(f_260, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, A, A)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => ((r2_relset_1(A, A, k1_partfun1(A, A, A, A, C, B), B) & v2_funct_1(B)) => r2_relset_1(A, A, C, k6_partfun1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_funct_2)).
% 34.07/24.05  tff(f_182, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 34.07/24.05  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 34.07/24.05  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 34.07/24.05  tff(f_83, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 34.07/24.05  tff(f_166, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 34.07/24.05  tff(f_48, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 34.07/24.05  tff(f_170, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 34.07/24.05  tff(f_240, axiom, (![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k1_relset_1(A, A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_2)).
% 34.07/24.05  tff(f_93, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 34.07/24.05  tff(f_194, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 34.07/24.05  tff(f_204, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 34.07/24.05  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 34.07/24.05  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 34.07/24.05  tff(f_67, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 34.07/24.05  tff(f_54, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 34.07/24.05  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 34.07/24.05  tff(f_206, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 34.07/24.05  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 34.07/24.05  tff(f_145, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 34.07/24.05  tff(f_174, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 34.07/24.05  tff(f_222, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 34.07/24.05  tff(f_232, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 34.07/24.05  tff(f_71, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 34.07/24.05  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 34.07/24.05  tff(f_135, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 34.07/24.05  tff(f_108, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(A) = k1_relat_1(B)) & (k5_relat_1(A, B) = A)) => (B = k6_relat_1(k1_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_funct_1)).
% 34.07/24.05  tff(f_160, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 34.07/24.05  tff(c_94, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_476, plain, (![A_121, B_122, D_123]: (r2_relset_1(A_121, B_122, D_123, D_123) | ~m1_subset_1(D_123, k1_zfmisc_1(k2_zfmisc_1(A_121, B_122))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 34.07/24.05  tff(c_485, plain, (r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_94, c_476])).
% 34.07/24.05  tff(c_18, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 34.07/24.05  tff(c_169, plain, (![B_82, A_83]: (v1_relat_1(B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_83)) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_42])).
% 34.07/24.05  tff(c_175, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_94, c_169])).
% 34.07/24.05  tff(c_182, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_175])).
% 34.07/24.05  tff(c_98, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_34, plain, (![A_21]: (v1_relat_1(k2_funct_1(A_21)) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_83])).
% 34.07/24.05  tff(c_248, plain, (![C_98, B_99, A_100]: (v5_relat_1(C_98, B_99) | ~m1_subset_1(C_98, k1_zfmisc_1(k2_zfmisc_1(A_100, B_99))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 34.07/24.05  tff(c_260, plain, (v5_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_94, c_248])).
% 34.07/24.05  tff(c_16, plain, (![B_9, A_8]: (r1_tarski(k2_relat_1(B_9), A_8) | ~v5_relat_1(B_9, A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 34.07/24.05  tff(c_96, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_808, plain, (![A_158, B_159, C_160]: (k1_relset_1(A_158, B_159, C_160)=k1_relat_1(C_160) | ~m1_subset_1(C_160, k1_zfmisc_1(k2_zfmisc_1(A_158, B_159))))), inference(cnfTransformation, [status(thm)], [f_170])).
% 34.07/24.05  tff(c_824, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_808])).
% 34.07/24.05  tff(c_1028, plain, (![A_189, B_190]: (k1_relset_1(A_189, A_189, B_190)=A_189 | ~m1_subset_1(B_190, k1_zfmisc_1(k2_zfmisc_1(A_189, A_189))) | ~v1_funct_2(B_190, A_189, A_189) | ~v1_funct_1(B_190))), inference(cnfTransformation, [status(thm)], [f_240])).
% 34.07/24.05  tff(c_1035, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_1028])).
% 34.07/24.05  tff(c_1042, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_824, c_1035])).
% 34.07/24.05  tff(c_36, plain, (![B_23, A_22]: (k10_relat_1(B_23, k9_relat_1(B_23, A_22))=A_22 | ~v2_funct_1(B_23) | ~r1_tarski(A_22, k1_relat_1(B_23)) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_93])).
% 34.07/24.05  tff(c_1049, plain, (![A_22]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_22))=A_22 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_22, '#skF_1') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1042, c_36])).
% 34.07/24.05  tff(c_1080, plain, (![A_22]: (k10_relat_1('#skF_3', k9_relat_1('#skF_3', A_22))=A_22 | ~v2_funct_1('#skF_3') | ~r1_tarski(A_22, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_1049])).
% 34.07/24.05  tff(c_2596, plain, (~v2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_1080])).
% 34.07/24.05  tff(c_100, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_178, plain, (v1_relat_1('#skF_2') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_100, c_169])).
% 34.07/24.05  tff(c_185, plain, (v1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_178])).
% 34.07/24.05  tff(c_104, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_90, plain, (v2_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_102, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_825, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_100, c_808])).
% 34.07/24.05  tff(c_1038, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_2')='#skF_1' | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_100, c_1028])).
% 34.07/24.05  tff(c_1045, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_825, c_1038])).
% 34.07/24.05  tff(c_2498, plain, (![B_248, E_251, F_246, D_247, C_250, A_249]: (m1_subset_1(k1_partfun1(A_249, B_248, C_250, D_247, E_251, F_246), k1_zfmisc_1(k2_zfmisc_1(A_249, D_247))) | ~m1_subset_1(F_246, k1_zfmisc_1(k2_zfmisc_1(C_250, D_247))) | ~v1_funct_1(F_246) | ~m1_subset_1(E_251, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))) | ~v1_funct_1(E_251))), inference(cnfTransformation, [status(thm)], [f_194])).
% 34.07/24.05  tff(c_92, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_1335, plain, (![D_195, C_196, A_197, B_198]: (D_195=C_196 | ~r2_relset_1(A_197, B_198, C_196, D_195) | ~m1_subset_1(D_195, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))) | ~m1_subset_1(C_196, k1_zfmisc_1(k2_zfmisc_1(A_197, B_198))))), inference(cnfTransformation, [status(thm)], [f_182])).
% 34.07/24.05  tff(c_1351, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_92, c_1335])).
% 34.07/24.05  tff(c_1376, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2' | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_1351])).
% 34.07/24.05  tff(c_1380, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_1376])).
% 34.07/24.05  tff(c_2520, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_2') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_2498, c_1380])).
% 34.07/24.05  tff(c_2555, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_94, c_104, c_100, c_2520])).
% 34.07/24.05  tff(c_2556, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_1376])).
% 34.07/24.05  tff(c_3412, plain, (![B_289, E_285, D_290, A_287, C_286, F_288]: (k1_partfun1(A_287, B_289, C_286, D_290, E_285, F_288)=k5_relat_1(E_285, F_288) | ~m1_subset_1(F_288, k1_zfmisc_1(k2_zfmisc_1(C_286, D_290))) | ~v1_funct_1(F_288) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_289))) | ~v1_funct_1(E_285))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.07/24.05  tff(c_3429, plain, (![A_287, B_289, E_285]: (k1_partfun1(A_287, B_289, '#skF_1', '#skF_1', E_285, '#skF_2')=k5_relat_1(E_285, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(A_287, B_289))) | ~v1_funct_1(E_285))), inference(resolution, [status(thm)], [c_100, c_3412])).
% 34.07/24.05  tff(c_3807, plain, (![A_300, B_301, E_302]: (k1_partfun1(A_300, B_301, '#skF_1', '#skF_1', E_302, '#skF_2')=k5_relat_1(E_302, '#skF_2') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))) | ~v1_funct_1(E_302))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_3429])).
% 34.07/24.05  tff(c_3841, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_3807])).
% 34.07/24.05  tff(c_3867, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2556, c_3841])).
% 34.07/24.05  tff(c_42, plain, (![B_29, A_27]: (v2_funct_1(B_29) | k2_relat_1(B_29)!=k1_relat_1(A_27) | ~v2_funct_1(k5_relat_1(B_29, A_27)) | ~v1_funct_1(B_29) | ~v1_relat_1(B_29) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_125])).
% 34.07/24.05  tff(c_3879, plain, (v2_funct_1('#skF_3') | k2_relat_1('#skF_3')!=k1_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3867, c_42])).
% 34.07/24.05  tff(c_3890, plain, (v2_funct_1('#skF_3') | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_182, c_98, c_90, c_1045, c_3879])).
% 34.07/24.05  tff(c_3891, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2596, c_3890])).
% 34.07/24.05  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.07/24.05  tff(c_217, plain, (![C_90, A_91, B_92]: (v4_relat_1(C_90, A_91) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_91, B_92))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 34.07/24.05  tff(c_230, plain, (v4_relat_1('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_100, c_217])).
% 34.07/24.05  tff(c_305, plain, (![B_108, A_109]: (k7_relat_1(B_108, A_109)=B_108 | ~v4_relat_1(B_108, A_109) | ~v1_relat_1(B_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.07/24.05  tff(c_311, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_230, c_305])).
% 34.07/24.05  tff(c_320, plain, (k7_relat_1('#skF_2', '#skF_1')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_185, c_311])).
% 34.07/24.05  tff(c_341, plain, (![B_112, A_113]: (k2_relat_1(k7_relat_1(B_112, A_113))=k9_relat_1(B_112, A_113) | ~v1_relat_1(B_112))), inference(cnfTransformation, [status(thm)], [f_54])).
% 34.07/24.05  tff(c_365, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_320, c_341])).
% 34.07/24.05  tff(c_373, plain, (k9_relat_1('#skF_2', '#skF_1')=k2_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_185, c_365])).
% 34.07/24.05  tff(c_1103, plain, (![A_22]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_22))=A_22 | ~v2_funct_1('#skF_2') | ~r1_tarski(A_22, '#skF_1') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1045, c_36])).
% 34.07/24.05  tff(c_2564, plain, (![A_252]: (k10_relat_1('#skF_2', k9_relat_1('#skF_2', A_252))=A_252 | ~r1_tarski(A_252, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_90, c_1103])).
% 34.07/24.05  tff(c_2581, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_373, c_2564])).
% 34.07/24.05  tff(c_2589, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2581])).
% 34.07/24.05  tff(c_22, plain, (![B_16, A_14]: (k9_relat_1(B_16, k2_relat_1(A_14))=k2_relat_1(k5_relat_1(A_14, B_16)) | ~v1_relat_1(B_16) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_61])).
% 34.07/24.05  tff(c_2578, plain, (![A_14]: (k10_relat_1('#skF_2', k2_relat_1(k5_relat_1(A_14, '#skF_2')))=k2_relat_1(A_14) | ~r1_tarski(k2_relat_1(A_14), '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(A_14))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2564])).
% 34.07/24.05  tff(c_2587, plain, (![A_14]: (k10_relat_1('#skF_2', k2_relat_1(k5_relat_1(A_14, '#skF_2')))=k2_relat_1(A_14) | ~r1_tarski(k2_relat_1(A_14), '#skF_1') | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_2578])).
% 34.07/24.05  tff(c_3874, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_3867, c_2587])).
% 34.07/24.05  tff(c_3886, plain, (k2_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_2589, c_3874])).
% 34.07/24.05  tff(c_3989, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_3891, c_3886])).
% 34.07/24.05  tff(c_3992, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_3989])).
% 34.07/24.05  tff(c_3996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_260, c_3992])).
% 34.07/24.05  tff(c_3998, plain, (v2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_1080])).
% 34.07/24.05  tff(c_72, plain, (![A_60]: (k6_relat_1(A_60)=k6_partfun1(A_60))), inference(cnfTransformation, [status(thm)], [f_206])).
% 34.07/24.05  tff(c_30, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.07/24.05  tff(c_108, plain, (![A_20]: (k2_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_30])).
% 34.07/24.05  tff(c_50, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_relat_1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_145])).
% 34.07/24.05  tff(c_105, plain, (![A_31]: (k5_relat_1(A_31, k2_funct_1(A_31))=k6_partfun1(k1_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_50])).
% 34.07/24.05  tff(c_660, plain, (![A_145, B_146, C_147]: (k2_relset_1(A_145, B_146, C_147)=k2_relat_1(C_147) | ~m1_subset_1(C_147, k1_zfmisc_1(k2_zfmisc_1(A_145, B_146))))), inference(cnfTransformation, [status(thm)], [f_174])).
% 34.07/24.05  tff(c_672, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_660])).
% 34.07/24.05  tff(c_4493, plain, (![C_321, B_322, A_323]: (v1_funct_2(k2_funct_1(C_321), B_322, A_323) | k2_relset_1(A_323, B_322, C_321)!=B_322 | ~v2_funct_1(C_321) | ~m1_subset_1(C_321, k1_zfmisc_1(k2_zfmisc_1(A_323, B_322))) | ~v1_funct_2(C_321, A_323, B_322) | ~v1_funct_1(C_321))), inference(cnfTransformation, [status(thm)], [f_222])).
% 34.07/24.05  tff(c_4512, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_4493])).
% 34.07/24.05  tff(c_4527, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | k2_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_3998, c_672, c_4512])).
% 34.07/24.05  tff(c_4577, plain, (k2_relat_1('#skF_3')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4527])).
% 34.07/24.05  tff(c_4706, plain, (![C_334, F_336, D_338, E_333, B_337, A_335]: (k1_partfun1(A_335, B_337, C_334, D_338, E_333, F_336)=k5_relat_1(E_333, F_336) | ~m1_subset_1(F_336, k1_zfmisc_1(k2_zfmisc_1(C_334, D_338))) | ~v1_funct_1(F_336) | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_335, B_337))) | ~v1_funct_1(E_333))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.07/24.05  tff(c_4721, plain, (![A_335, B_337, E_333]: (k1_partfun1(A_335, B_337, '#skF_1', '#skF_1', E_333, '#skF_2')=k5_relat_1(E_333, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_333, k1_zfmisc_1(k2_zfmisc_1(A_335, B_337))) | ~v1_funct_1(E_333))), inference(resolution, [status(thm)], [c_100, c_4706])).
% 34.07/24.05  tff(c_5173, plain, (![A_356, B_357, E_358]: (k1_partfun1(A_356, B_357, '#skF_1', '#skF_1', E_358, '#skF_2')=k5_relat_1(E_358, '#skF_2') | ~m1_subset_1(E_358, k1_zfmisc_1(k2_zfmisc_1(A_356, B_357))) | ~v1_funct_1(E_358))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_4721])).
% 34.07/24.05  tff(c_5201, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_5173])).
% 34.07/24.05  tff(c_5221, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2556, c_5201])).
% 34.07/24.05  tff(c_5228, plain, (k10_relat_1('#skF_2', k2_relat_1('#skF_2'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5221, c_2587])).
% 34.07/24.05  tff(c_5240, plain, (k2_relat_1('#skF_3')='#skF_1' | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_2589, c_5228])).
% 34.07/24.05  tff(c_5241, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_4577, c_5240])).
% 34.07/24.05  tff(c_5251, plain, (~v5_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_16, c_5241])).
% 34.07/24.05  tff(c_5255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_260, c_5251])).
% 34.07/24.05  tff(c_5257, plain, (k2_relat_1('#skF_3')='#skF_1'), inference(splitRight, [status(thm)], [c_4527])).
% 34.07/24.05  tff(c_5291, plain, (![B_16]: (k2_relat_1(k5_relat_1('#skF_3', B_16))=k9_relat_1(B_16, '#skF_1') | ~v1_relat_1(B_16) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_5257, c_22])).
% 34.07/24.05  tff(c_5704, plain, (![B_386]: (k2_relat_1(k5_relat_1('#skF_3', B_386))=k9_relat_1(B_386, '#skF_1') | ~v1_relat_1(B_386))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_5291])).
% 34.07/24.05  tff(c_5758, plain, (k2_relat_1(k6_partfun1(k1_relat_1('#skF_3')))=k9_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_105, c_5704])).
% 34.07/24.05  tff(c_5768, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_1')='#skF_1' | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_108, c_1042, c_5758])).
% 34.07/24.05  tff(c_5769, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5768])).
% 34.07/24.05  tff(c_5838, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_5769])).
% 34.07/24.05  tff(c_5842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_5838])).
% 34.07/24.05  tff(c_5844, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5768])).
% 34.07/24.05  tff(c_82, plain, (![A_64]: (v1_funct_2(A_64, k1_relat_1(A_64), k2_relat_1(A_64)) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_232])).
% 34.07/24.05  tff(c_1067, plain, (v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1042, c_82])).
% 34.07/24.05  tff(c_1092, plain, (v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_1067])).
% 34.07/24.05  tff(c_26, plain, (![A_19]: (r1_tarski(A_19, k2_zfmisc_1(k1_relat_1(A_19), k2_relat_1(A_19))) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.07/24.05  tff(c_1076, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3'))) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1042, c_26])).
% 34.07/24.05  tff(c_1098, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_1076])).
% 34.07/24.05  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 34.07/24.05  tff(c_671, plain, (![A_145, B_146, A_3]: (k2_relset_1(A_145, B_146, A_3)=k2_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_145, B_146)))), inference(resolution, [status(thm)], [c_10, c_660])).
% 34.07/24.05  tff(c_1225, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1098, c_671])).
% 34.07/24.05  tff(c_80, plain, (![A_64]: (m1_subset_1(A_64, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_64), k2_relat_1(A_64)))) | ~v1_funct_1(A_64) | ~v1_relat_1(A_64))), inference(cnfTransformation, [status(thm)], [f_232])).
% 34.07/24.05  tff(c_1058, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3')))) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1042, c_80])).
% 34.07/24.05  tff(c_1086, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_1058])).
% 34.07/24.05  tff(c_4389, plain, (![C_318, A_319, B_320]: (v1_funct_1(k2_funct_1(C_318)) | k2_relset_1(A_319, B_320, C_318)!=B_320 | ~v2_funct_1(C_318) | ~m1_subset_1(C_318, k1_zfmisc_1(k2_zfmisc_1(A_319, B_320))) | ~v1_funct_2(C_318, A_319, B_320) | ~v1_funct_1(C_318))), inference(cnfTransformation, [status(thm)], [f_222])).
% 34.07/24.05  tff(c_4395, plain, (v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', k2_relat_1('#skF_3'), '#skF_3')!=k2_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', k2_relat_1('#skF_3')) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1086, c_4389])).
% 34.07/24.05  tff(c_4415, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_1092, c_3998, c_1225, c_4395])).
% 34.07/24.05  tff(c_44, plain, (![A_30]: (k2_relat_1(k2_funct_1(A_30))=k1_relat_1(A_30) | ~v2_funct_1(A_30) | ~v1_funct_1(A_30) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_135])).
% 34.07/24.05  tff(c_513, plain, (![A_130]: (k1_relat_1(k2_funct_1(A_130))=k2_relat_1(A_130) | ~v2_funct_1(A_130) | ~v1_funct_1(A_130) | ~v1_relat_1(A_130))), inference(cnfTransformation, [status(thm)], [f_135])).
% 34.07/24.05  tff(c_47030, plain, (![A_1226]: (r1_tarski(k2_funct_1(A_1226), k2_zfmisc_1(k2_relat_1(A_1226), k2_relat_1(k2_funct_1(A_1226)))) | ~v1_relat_1(k2_funct_1(A_1226)) | ~v2_funct_1(A_1226) | ~v1_funct_1(A_1226) | ~v1_relat_1(A_1226))), inference(superposition, [status(thm), theory('equality')], [c_513, c_26])).
% 34.07/24.05  tff(c_47064, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5257, c_47030])).
% 34.07/24.05  tff(c_47101, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_5844, c_47064])).
% 34.07/24.05  tff(c_259, plain, (![A_3, B_99, A_100]: (v5_relat_1(A_3, B_99) | ~r1_tarski(A_3, k2_zfmisc_1(A_100, B_99)))), inference(resolution, [status(thm)], [c_10, c_248])).
% 34.07/24.05  tff(c_47143, plain, (v5_relat_1(k2_funct_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3')))), inference(resolution, [status(thm)], [c_47101, c_259])).
% 34.07/24.05  tff(c_47164, plain, (v5_relat_1(k2_funct_1('#skF_3'), k1_relat_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_47143])).
% 34.07/24.05  tff(c_47172, plain, (v5_relat_1(k2_funct_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_1042, c_47164])).
% 34.07/24.05  tff(c_573, plain, (![A_137]: (k2_relat_1(k2_funct_1(A_137))=k1_relat_1(A_137) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(cnfTransformation, [status(thm)], [f_135])).
% 34.07/24.05  tff(c_588, plain, (![A_137, A_8]: (r1_tarski(k1_relat_1(A_137), A_8) | ~v5_relat_1(k2_funct_1(A_137), A_8) | ~v1_relat_1(k2_funct_1(A_137)) | ~v2_funct_1(A_137) | ~v1_funct_1(A_137) | ~v1_relat_1(A_137))), inference(superposition, [status(thm), theory('equality')], [c_573, c_16])).
% 34.07/24.05  tff(c_47159, plain, (r1_tarski(k1_relat_1('#skF_3'), k2_relat_1(k2_funct_1('#skF_3'))) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_47143, c_588])).
% 34.07/24.05  tff(c_47167, plain, (r1_tarski('#skF_1', k2_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_5844, c_1042, c_47159])).
% 34.07/24.05  tff(c_262, plain, (![B_101, A_102]: (r1_tarski(k2_relat_1(B_101), A_102) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(cnfTransformation, [status(thm)], [f_48])).
% 34.07/24.05  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 34.07/24.05  tff(c_281, plain, (![B_101, A_102]: (k2_relat_1(B_101)=A_102 | ~r1_tarski(A_102, k2_relat_1(B_101)) | ~v5_relat_1(B_101, A_102) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_262, c_2])).
% 34.07/24.05  tff(c_47276, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1' | ~v5_relat_1(k2_funct_1('#skF_3'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_47167, c_281])).
% 34.07/24.05  tff(c_47288, plain, (k2_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_47172, c_47276])).
% 34.07/24.05  tff(c_48, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_relat_1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(cnfTransformation, [status(thm)], [f_145])).
% 34.07/24.05  tff(c_106, plain, (![A_31]: (k5_relat_1(k2_funct_1(A_31), A_31)=k6_partfun1(k2_relat_1(A_31)) | ~v2_funct_1(A_31) | ~v1_funct_1(A_31) | ~v1_relat_1(A_31))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_48])).
% 34.07/24.05  tff(c_5256, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4527])).
% 34.07/24.05  tff(c_47133, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_1', k1_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_44, c_47101])).
% 34.07/24.05  tff(c_47150, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_1042, c_47133])).
% 34.07/24.05  tff(c_1039, plain, (![A_189, A_3]: (k1_relset_1(A_189, A_189, A_3)=A_189 | ~v1_funct_2(A_3, A_189, A_189) | ~v1_funct_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_189, A_189)))), inference(resolution, [status(thm)], [c_10, c_1028])).
% 34.07/24.05  tff(c_47605, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1' | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_47150, c_1039])).
% 34.07/24.05  tff(c_47636, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4415, c_5256, c_47605])).
% 34.07/24.05  tff(c_823, plain, (![A_158, B_159, A_3]: (k1_relset_1(A_158, B_159, A_3)=k1_relat_1(A_3) | ~r1_tarski(A_3, k2_zfmisc_1(A_158, B_159)))), inference(resolution, [status(thm)], [c_10, c_808])).
% 34.07/24.05  tff(c_47637, plain, (k1_relset_1('#skF_1', '#skF_1', k2_funct_1('#skF_3'))=k1_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_47150, c_823])).
% 34.07/24.05  tff(c_47980, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_47636, c_47637])).
% 34.07/24.05  tff(c_48022, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1(k2_funct_1('#skF_3'))))) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_47980, c_80])).
% 34.07/24.05  tff(c_48072, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_4415, c_47288, c_48022])).
% 34.07/24.05  tff(c_5268, plain, (k2_relset_1('#skF_1', '#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5257, c_672])).
% 34.07/24.05  tff(c_74, plain, (![C_63, B_62, A_61]: (m1_subset_1(k2_funct_1(C_63), k1_zfmisc_1(k2_zfmisc_1(B_62, A_61))) | k2_relset_1(A_61, B_62, C_63)!=B_62 | ~v2_funct_1(C_63) | ~m1_subset_1(C_63, k1_zfmisc_1(k2_zfmisc_1(A_61, B_62))) | ~v1_funct_2(C_63, A_61, B_62) | ~v1_funct_1(C_63))), inference(cnfTransformation, [status(thm)], [f_222])).
% 34.07/24.05  tff(c_5451, plain, (![E_370, B_374, C_371, A_372, F_373, D_375]: (k1_partfun1(A_372, B_374, C_371, D_375, E_370, F_373)=k5_relat_1(E_370, F_373) | ~m1_subset_1(F_373, k1_zfmisc_1(k2_zfmisc_1(C_371, D_375))) | ~v1_funct_1(F_373) | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_372, B_374))) | ~v1_funct_1(E_370))), inference(cnfTransformation, [status(thm)], [f_204])).
% 34.07/24.05  tff(c_5462, plain, (![A_372, B_374, E_370]: (k1_partfun1(A_372, B_374, '#skF_1', '#skF_1', E_370, '#skF_3')=k5_relat_1(E_370, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_372, B_374))) | ~v1_funct_1(E_370))), inference(resolution, [status(thm)], [c_94, c_5451])).
% 34.07/24.05  tff(c_6038, plain, (![A_400, B_401, E_402]: (k1_partfun1(A_400, B_401, '#skF_1', '#skF_1', E_402, '#skF_3')=k5_relat_1(E_402, '#skF_3') | ~m1_subset_1(E_402, k1_zfmisc_1(k2_zfmisc_1(A_400, B_401))) | ~v1_funct_1(E_402))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_5462])).
% 34.07/24.05  tff(c_61652, plain, (![B_1501, A_1502, C_1503]: (k1_partfun1(B_1501, A_1502, '#skF_1', '#skF_1', k2_funct_1(C_1503), '#skF_3')=k5_relat_1(k2_funct_1(C_1503), '#skF_3') | ~v1_funct_1(k2_funct_1(C_1503)) | k2_relset_1(A_1502, B_1501, C_1503)!=B_1501 | ~v2_funct_1(C_1503) | ~m1_subset_1(C_1503, k1_zfmisc_1(k2_zfmisc_1(A_1502, B_1501))) | ~v1_funct_2(C_1503, A_1502, B_1501) | ~v1_funct_1(C_1503))), inference(resolution, [status(thm)], [c_74, c_6038])).
% 34.07/24.05  tff(c_61686, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | k2_relset_1('#skF_1', '#skF_1', '#skF_3')!='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_61652])).
% 34.07/24.05  tff(c_61712, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', k2_funct_1('#skF_3'), '#skF_3')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_98, c_96, c_3998, c_5268, c_4415, c_61686])).
% 34.07/24.05  tff(c_66, plain, (![B_49, F_53, A_48, D_51, E_52, C_50]: (m1_subset_1(k1_partfun1(A_48, B_49, C_50, D_51, E_52, F_53), k1_zfmisc_1(k2_zfmisc_1(A_48, D_51))) | ~m1_subset_1(F_53, k1_zfmisc_1(k2_zfmisc_1(C_50, D_51))) | ~v1_funct_1(F_53) | ~m1_subset_1(E_52, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))) | ~v1_funct_1(E_52))), inference(cnfTransformation, [status(thm)], [f_194])).
% 34.07/24.05  tff(c_61897, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_61712, c_66])).
% 34.07/24.05  tff(c_61901, plain, (m1_subset_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4415, c_48072, c_98, c_94, c_61897])).
% 34.07/24.05  tff(c_12, plain, (![B_7, A_5]: (v1_relat_1(B_7) | ~m1_subset_1(B_7, k1_zfmisc_1(A_5)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 34.07/24.05  tff(c_61967, plain, (v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_1'))), inference(resolution, [status(thm)], [c_61901, c_12])).
% 34.07/24.05  tff(c_62017, plain, (v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_61967])).
% 34.07/24.05  tff(c_62023, plain, (v1_relat_1(k6_partfun1(k2_relat_1('#skF_3'))) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_106, c_62017])).
% 34.07/24.05  tff(c_62025, plain, (v1_relat_1(k6_partfun1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_5257, c_62023])).
% 34.07/24.05  tff(c_28, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_75])).
% 34.07/24.05  tff(c_109, plain, (![A_20]: (k1_relat_1(k6_partfun1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_28])).
% 34.07/24.05  tff(c_382, plain, (![A_114]: (r1_tarski(A_114, k2_zfmisc_1(k1_relat_1(A_114), k2_relat_1(A_114))) | ~v1_relat_1(A_114))), inference(cnfTransformation, [status(thm)], [f_71])).
% 34.07/24.05  tff(c_228, plain, (![A_3, A_91, B_92]: (v4_relat_1(A_3, A_91) | ~r1_tarski(A_3, k2_zfmisc_1(A_91, B_92)))), inference(resolution, [status(thm)], [c_10, c_217])).
% 34.07/24.05  tff(c_417, plain, (![A_115]: (v4_relat_1(A_115, k1_relat_1(A_115)) | ~v1_relat_1(A_115))), inference(resolution, [status(thm)], [c_382, c_228])).
% 34.07/24.05  tff(c_440, plain, (![A_117]: (v4_relat_1(k6_partfun1(A_117), A_117) | ~v1_relat_1(k6_partfun1(A_117)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_417])).
% 34.07/24.05  tff(c_24, plain, (![B_18, A_17]: (k7_relat_1(B_18, A_17)=B_18 | ~v4_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 34.07/24.05  tff(c_444, plain, (![A_117]: (k7_relat_1(k6_partfun1(A_117), A_117)=k6_partfun1(A_117) | ~v1_relat_1(k6_partfun1(A_117)))), inference(resolution, [status(thm)], [c_440, c_24])).
% 34.07/24.05  tff(c_62164, plain, (k7_relat_1(k6_partfun1('#skF_1'), '#skF_1')=k6_partfun1('#skF_1')), inference(resolution, [status(thm)], [c_62025, c_444])).
% 34.07/24.05  tff(c_56, plain, (![C_37, A_35, B_36]: (v4_relat_1(C_37, A_35) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_166])).
% 34.07/24.05  tff(c_62014, plain, (v4_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_61901, c_56])).
% 34.07/24.05  tff(c_62280, plain, (k7_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), '#skF_1')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v1_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_62014, c_24])).
% 34.07/24.05  tff(c_62286, plain, (k7_relat_1(k5_relat_1(k2_funct_1('#skF_3'), '#skF_3'), '#skF_1')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62017, c_62280])).
% 34.07/24.05  tff(c_76461, plain, (k7_relat_1(k6_partfun1(k2_relat_1('#skF_3')), '#skF_1')=k5_relat_1(k2_funct_1('#skF_3'), '#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_106, c_62286])).
% 34.07/24.05  tff(c_76481, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_3998, c_62164, c_5257, c_76461])).
% 34.07/24.05  tff(c_38, plain, (![B_26, A_24]: (k6_relat_1(k1_relat_1(B_26))=B_26 | k5_relat_1(A_24, B_26)!=A_24 | k2_relat_1(A_24)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_108])).
% 34.07/24.05  tff(c_107, plain, (![B_26, A_24]: (k6_partfun1(k1_relat_1(B_26))=B_26 | k5_relat_1(A_24, B_26)!=A_24 | k2_relat_1(A_24)!=k1_relat_1(B_26) | ~v1_funct_1(B_26) | ~v1_relat_1(B_26) | ~v1_funct_1(A_24) | ~v1_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_38])).
% 34.07/24.05  tff(c_76508, plain, (k6_partfun1(k1_relat_1('#skF_3'))='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_3'))!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3') | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_76481, c_107])).
% 34.07/24.05  tff(c_76530, plain, (k6_partfun1('#skF_1')='#skF_3' | k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5844, c_4415, c_182, c_98, c_1042, c_47288, c_1042, c_76508])).
% 34.07/24.05  tff(c_76654, plain, (k6_partfun1('#skF_1')!=k2_funct_1('#skF_3')), inference(splitLeft, [status(thm)], [c_76530])).
% 34.07/24.05  tff(c_4120, plain, (![A_311]: (k10_relat_1('#skF_2', k2_relat_1(k5_relat_1(A_311, '#skF_2')))=k2_relat_1(A_311) | ~r1_tarski(k2_relat_1(A_311), '#skF_1') | ~v1_relat_1(A_311))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_2578])).
% 34.07/24.05  tff(c_4134, plain, (k10_relat_1('#skF_2', k2_relat_1(k6_partfun1(k2_relat_1('#skF_2'))))=k2_relat_1(k2_funct_1('#skF_2')) | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_106, c_4120])).
% 34.07/24.05  tff(c_4140, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1' | ~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_90, c_2589, c_108, c_4134])).
% 34.07/24.05  tff(c_4141, plain, (~v1_relat_1(k2_funct_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_4140])).
% 34.07/24.05  tff(c_4144, plain, (~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_4141])).
% 34.07/24.05  tff(c_4148, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_4144])).
% 34.07/24.05  tff(c_4150, plain, (v1_relat_1(k2_funct_1('#skF_2'))), inference(splitRight, [status(thm)], [c_4140])).
% 34.07/24.05  tff(c_1121, plain, (v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_82])).
% 34.07/24.05  tff(c_1146, plain, (v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_1121])).
% 34.07/24.05  tff(c_1130, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_26])).
% 34.07/24.05  tff(c_1152, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_1130])).
% 34.07/24.05  tff(c_1190, plain, (k2_relset_1('#skF_1', k2_relat_1('#skF_2'), '#skF_2')=k2_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1152, c_671])).
% 34.07/24.05  tff(c_1112, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2')))) | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1045, c_80])).
% 34.07/24.05  tff(c_1140, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_1112])).
% 34.07/24.05  tff(c_4398, plain, (v1_funct_1(k2_funct_1('#skF_2')) | k2_relset_1('#skF_1', k2_relat_1('#skF_2'), '#skF_2')!=k2_relat_1('#skF_2') | ~v2_funct_1('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_1140, c_4389])).
% 34.07/24.05  tff(c_4418, plain, (v1_funct_1(k2_funct_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1146, c_90, c_1190, c_4398])).
% 34.07/24.05  tff(c_4149, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1') | k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_4140])).
% 34.07/24.05  tff(c_4151, plain, (~r1_tarski(k2_relat_1(k2_funct_1('#skF_2')), '#skF_1')), inference(splitLeft, [status(thm)], [c_4149])).
% 34.07/24.05  tff(c_4154, plain, (~r1_tarski(k1_relat_1('#skF_2'), '#skF_1') | ~v2_funct_1('#skF_2') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_44, c_4151])).
% 34.07/24.05  tff(c_4160, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_185, c_104, c_90, c_6, c_1045, c_4154])).
% 34.07/24.05  tff(c_4161, plain, (k2_relat_1(k2_funct_1('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_4149])).
% 34.07/24.05  tff(c_5464, plain, (![A_372, B_374, E_370]: (k1_partfun1(A_372, B_374, '#skF_1', '#skF_1', E_370, '#skF_2')=k5_relat_1(E_370, '#skF_2') | ~v1_funct_1('#skF_2') | ~m1_subset_1(E_370, k1_zfmisc_1(k2_zfmisc_1(A_372, B_374))) | ~v1_funct_1(E_370))), inference(resolution, [status(thm)], [c_100, c_5451])).
% 34.07/24.05  tff(c_5644, plain, (![A_383, B_384, E_385]: (k1_partfun1(A_383, B_384, '#skF_1', '#skF_1', E_385, '#skF_2')=k5_relat_1(E_385, '#skF_2') | ~m1_subset_1(E_385, k1_zfmisc_1(k2_zfmisc_1(A_383, B_384))) | ~v1_funct_1(E_385))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_5464])).
% 34.07/24.05  tff(c_5663, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_3', '#skF_2')=k5_relat_1('#skF_3', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_94, c_5644])).
% 34.07/24.05  tff(c_5676, plain, (k5_relat_1('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_2556, c_5663])).
% 34.07/24.05  tff(c_4163, plain, (![B_312, A_313]: (k5_relat_1(k2_funct_1(B_312), k2_funct_1(A_313))=k2_funct_1(k5_relat_1(A_313, B_312)) | ~v2_funct_1(B_312) | ~v2_funct_1(A_313) | ~v1_funct_1(B_312) | ~v1_relat_1(B_312) | ~v1_funct_1(A_313) | ~v1_relat_1(A_313))), inference(cnfTransformation, [status(thm)], [f_160])).
% 34.07/24.05  tff(c_92587, plain, (![A_2070, B_2071]: (k6_partfun1(k1_relat_1(k2_funct_1(A_2070)))=k2_funct_1(A_2070) | k2_funct_1(k5_relat_1(A_2070, B_2071))!=k2_funct_1(B_2071) | k2_relat_1(k2_funct_1(B_2071))!=k1_relat_1(k2_funct_1(A_2070)) | ~v1_funct_1(k2_funct_1(A_2070)) | ~v1_relat_1(k2_funct_1(A_2070)) | ~v1_funct_1(k2_funct_1(B_2071)) | ~v1_relat_1(k2_funct_1(B_2071)) | ~v2_funct_1(B_2071) | ~v2_funct_1(A_2070) | ~v1_funct_1(B_2071) | ~v1_relat_1(B_2071) | ~v1_funct_1(A_2070) | ~v1_relat_1(A_2070))), inference(superposition, [status(thm), theory('equality')], [c_4163, c_107])).
% 34.07/24.05  tff(c_92603, plain, (k6_partfun1(k1_relat_1(k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | k2_relat_1(k2_funct_1('#skF_2'))!=k1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v1_funct_1(k2_funct_1('#skF_2')) | ~v1_relat_1(k2_funct_1('#skF_2')) | ~v2_funct_1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_2') | ~v1_relat_1('#skF_2') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5676, c_92587])).
% 34.07/24.05  tff(c_92626, plain, (k6_partfun1('#skF_1')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_182, c_98, c_185, c_104, c_3998, c_90, c_4150, c_4418, c_5844, c_4415, c_4161, c_47980, c_47980, c_92603])).
% 34.07/24.05  tff(c_92628, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76654, c_92626])).
% 34.07/24.05  tff(c_92629, plain, (k6_partfun1('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_76530])).
% 34.07/24.05  tff(c_88, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_260])).
% 34.07/24.05  tff(c_92650, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_92629, c_88])).
% 34.07/24.05  tff(c_92669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_485, c_92650])).
% 34.07/24.05  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 34.07/24.05  
% 34.07/24.05  Inference rules
% 34.07/24.05  ----------------------
% 34.07/24.05  #Ref     : 0
% 34.07/24.05  #Sup     : 20009
% 34.07/24.05  #Fact    : 0
% 34.07/24.05  #Define  : 0
% 34.07/24.05  #Split   : 104
% 34.07/24.05  #Chain   : 0
% 34.07/24.05  #Close   : 0
% 34.07/24.05  
% 34.07/24.05  Ordering : KBO
% 34.07/24.05  
% 34.07/24.05  Simplification rules
% 34.07/24.05  ----------------------
% 34.07/24.05  #Subsume      : 1816
% 34.07/24.05  #Demod        : 35272
% 34.07/24.05  #Tautology    : 5285
% 34.07/24.05  #SimpNegUnit  : 130
% 34.07/24.05  #BackRed      : 331
% 34.07/24.05  
% 34.07/24.05  #Partial instantiations: 0
% 34.07/24.05  #Strategies tried      : 1
% 34.07/24.05  
% 34.07/24.05  Timing (in seconds)
% 34.07/24.05  ----------------------
% 34.07/24.05  Preprocessing        : 0.40
% 34.07/24.05  Parsing              : 0.21
% 34.07/24.05  CNF conversion       : 0.03
% 34.07/24.05  Main loop            : 22.78
% 34.07/24.05  Inferencing          : 4.20
% 34.07/24.05  Reduction            : 12.49
% 34.07/24.05  Demodulation         : 10.77
% 34.07/24.05  BG Simplification    : 0.33
% 34.07/24.05  Subsumption          : 4.70
% 34.07/24.05  Abstraction          : 0.53
% 34.07/24.05  MUC search           : 0.00
% 34.07/24.05  Cooper               : 0.00
% 34.07/24.05  Total                : 23.26
% 34.07/24.05  Index Insertion      : 0.00
% 34.07/24.05  Index Deletion       : 0.00
% 34.07/24.05  Index Matching       : 0.00
% 34.07/24.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
