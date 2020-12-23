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
% DateTime   : Thu Dec  3 10:13:12 EST 2020

% Result     : Theorem 10.38s
% Output     : CNFRefutation 10.57s
% Verified   : 
% Statistics : Number of formulae       :  156 (7275 expanded)
%              Number of leaves         :   49 (2603 expanded)
%              Depth                    :   19
%              Number of atoms          :  428 (31961 expanded)
%              Number of equality atoms :  109 (8841 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_278,negated_conjecture,(
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

tff(f_143,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_165,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_177,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_153,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_151,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_175,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_236,axiom,(
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

tff(f_96,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_220,axiom,(
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

tff(f_194,axiom,(
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

tff(f_106,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_252,axiom,(
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

tff(f_94,axiom,(
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

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_116,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k1_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A)
          & k2_relat_1(k5_relat_1(A,k2_funct_1(A))) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t58_funct_1)).

tff(f_133,axiom,(
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

tff(c_88,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_110,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_98,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_106,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_312,plain,(
    ! [A_110,B_111,C_112] :
      ( k2_relset_1(A_110,B_111,C_112) = k2_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_318,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_312])).

tff(c_325,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_318])).

tff(c_104,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_100,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_1791,plain,(
    ! [B_222,D_221,F_219,E_224,A_220,C_223] :
      ( m1_subset_1(k1_partfun1(A_220,B_222,C_223,D_221,E_224,F_219),k1_zfmisc_1(k2_zfmisc_1(A_220,D_221)))
      | ~ m1_subset_1(F_219,k1_zfmisc_1(k2_zfmisc_1(C_223,D_221)))
      | ~ v1_funct_1(F_219)
      | ~ m1_subset_1(E_224,k1_zfmisc_1(k2_zfmisc_1(A_220,B_222)))
      | ~ v1_funct_1(E_224) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    ! [A_48] : k6_relat_1(A_48) = k6_partfun1(A_48) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_58,plain,(
    ! [A_35] : m1_subset_1(k6_relat_1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_111,plain,(
    ! [A_35] : m1_subset_1(k6_partfun1(A_35),k1_zfmisc_1(k2_zfmisc_1(A_35,A_35))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_58])).

tff(c_96,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_662,plain,(
    ! [D_142,C_143,A_144,B_145] :
      ( D_142 = C_143
      | ~ r2_relset_1(A_144,B_145,C_143,D_142)
      | ~ m1_subset_1(D_142,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_670,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_96,c_662])).

tff(c_685,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_670])).

tff(c_768,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_685])).

tff(c_1823,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1791,c_768])).

tff(c_1861,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_106,c_104,c_100,c_1823])).

tff(c_1862,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_685])).

tff(c_7635,plain,(
    ! [F_571,B_569,C_572,D_568,A_570,E_567] :
      ( k1_partfun1(A_570,B_569,C_572,D_568,E_567,F_571) = k5_relat_1(E_567,F_571)
      | ~ m1_subset_1(F_571,k1_zfmisc_1(k2_zfmisc_1(C_572,D_568)))
      | ~ v1_funct_1(F_571)
      | ~ m1_subset_1(E_567,k1_zfmisc_1(k2_zfmisc_1(A_570,B_569)))
      | ~ v1_funct_1(E_567) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_7641,plain,(
    ! [A_570,B_569,E_567] :
      ( k1_partfun1(A_570,B_569,'#skF_2','#skF_1',E_567,'#skF_4') = k5_relat_1(E_567,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_567,k1_zfmisc_1(k2_zfmisc_1(A_570,B_569)))
      | ~ v1_funct_1(E_567) ) ),
    inference(resolution,[status(thm)],[c_100,c_7635])).

tff(c_7933,plain,(
    ! [A_587,B_588,E_589] :
      ( k1_partfun1(A_587,B_588,'#skF_2','#skF_1',E_589,'#skF_4') = k5_relat_1(E_589,'#skF_4')
      | ~ m1_subset_1(E_589,k1_zfmisc_1(k2_zfmisc_1(A_587,B_588)))
      | ~ v1_funct_1(E_589) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_7641])).

tff(c_7942,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_106,c_7933])).

tff(c_7950,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_1862,c_7942])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_161,plain,(
    ! [B_79,A_80] :
      ( v1_relat_1(B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_80))
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_167,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_106,c_161])).

tff(c_176,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_167])).

tff(c_170,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_100,c_161])).

tff(c_179,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_170])).

tff(c_24,plain,(
    ! [A_14] :
      ( v1_relat_1(k2_funct_1(A_14))
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_102,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_326,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_312])).

tff(c_2041,plain,(
    ! [C_233,A_234,B_235] :
      ( v1_funct_1(k2_funct_1(C_233))
      | k2_relset_1(A_234,B_235,C_233) != B_235
      | ~ v2_funct_1(C_233)
      | ~ m1_subset_1(C_233,k1_zfmisc_1(k2_zfmisc_1(A_234,B_235)))
      | ~ v1_funct_2(C_233,A_234,B_235)
      | ~ v1_funct_1(C_233) ) ),
    inference(cnfTransformation,[status(thm)],[f_236])).

tff(c_2050,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_2041])).

tff(c_2059,plain,
    ( v1_funct_1(k2_funct_1('#skF_4'))
    | k2_relat_1('#skF_4') != '#skF_1'
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_326,c_2050])).

tff(c_2068,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2059])).

tff(c_92,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_108,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_278])).

tff(c_36,plain,(
    ! [A_19] : v2_funct_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_113,plain,(
    ! [A_19] : v2_funct_1(k6_partfun1(A_19)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_36])).

tff(c_4261,plain,(
    ! [B_363,C_361,E_365,A_362,D_364] :
      ( k1_xboole_0 = C_361
      | v2_funct_1(E_365)
      | k2_relset_1(A_362,B_363,D_364) != B_363
      | ~ v2_funct_1(k1_partfun1(A_362,B_363,B_363,C_361,D_364,E_365))
      | ~ m1_subset_1(E_365,k1_zfmisc_1(k2_zfmisc_1(B_363,C_361)))
      | ~ v1_funct_2(E_365,B_363,C_361)
      | ~ v1_funct_1(E_365)
      | ~ m1_subset_1(D_364,k1_zfmisc_1(k2_zfmisc_1(A_362,B_363)))
      | ~ v1_funct_2(D_364,A_362,B_363)
      | ~ v1_funct_1(D_364) ) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_4267,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_4261])).

tff(c_4275,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_108,c_106,c_104,c_102,c_100,c_113,c_98,c_4267])).

tff(c_4277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2068,c_92,c_4275])).

tff(c_4279,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2059])).

tff(c_4278,plain,
    ( k2_relat_1('#skF_4') != '#skF_1'
    | v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_2059])).

tff(c_4280,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_4278])).

tff(c_267,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_relset_1(A_101,B_102,D_103,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_151])).

tff(c_274,plain,(
    ! [A_35] : r2_relset_1(A_35,A_35,k6_partfun1(A_35),k6_partfun1(A_35)) ),
    inference(resolution,[status(thm)],[c_111,c_267])).

tff(c_6545,plain,(
    ! [A_498,B_499,C_500,D_501] :
      ( k2_relset_1(A_498,B_499,C_500) = B_499
      | ~ r2_relset_1(B_499,B_499,k1_partfun1(B_499,A_498,A_498,B_499,D_501,C_500),k6_partfun1(B_499))
      | ~ m1_subset_1(D_501,k1_zfmisc_1(k2_zfmisc_1(B_499,A_498)))
      | ~ v1_funct_2(D_501,B_499,A_498)
      | ~ v1_funct_1(D_501)
      | ~ m1_subset_1(C_500,k1_zfmisc_1(k2_zfmisc_1(A_498,B_499)))
      | ~ v1_funct_2(C_500,A_498,B_499)
      | ~ v1_funct_1(C_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_194])).

tff(c_6551,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1862,c_6545])).

tff(c_6555,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_100,c_110,c_108,c_106,c_274,c_326,c_6551])).

tff(c_6557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4280,c_6555])).

tff(c_6559,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4278])).

tff(c_294,plain,(
    ! [A_109] :
      ( k1_relat_1(k2_funct_1(A_109)) = k2_relat_1(A_109)
      | ~ v2_funct_1(A_109)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    ! [B_92,A_93] :
      ( v4_relat_1(B_92,A_93)
      | ~ r1_tarski(k1_relat_1(B_92),A_93)
      | ~ v1_relat_1(B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_232,plain,(
    ! [B_92] :
      ( v4_relat_1(B_92,k1_relat_1(B_92))
      | ~ v1_relat_1(B_92) ) ),
    inference(resolution,[status(thm)],[c_6,c_218])).

tff(c_300,plain,(
    ! [A_109] :
      ( v4_relat_1(k2_funct_1(A_109),k2_relat_1(A_109))
      | ~ v1_relat_1(k2_funct_1(A_109))
      | ~ v2_funct_1(A_109)
      | ~ v1_funct_1(A_109)
      | ~ v1_relat_1(A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_232])).

tff(c_6567,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6559,c_300])).

tff(c_6576,plain,
    ( v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_104,c_4279,c_6567])).

tff(c_6584,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6576])).

tff(c_6587,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_6584])).

tff(c_6591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_104,c_6587])).

tff(c_6593,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6576])).

tff(c_6558,plain,(
    v1_funct_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4278])).

tff(c_6592,plain,(
    v4_relat_1(k2_funct_1('#skF_4'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_6576])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k1_relat_1(B_7),A_6)
      | ~ v4_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_606,plain,(
    ! [A_139,A_140] :
      ( r1_tarski(k2_relat_1(A_139),A_140)
      | ~ v4_relat_1(k2_funct_1(A_139),A_140)
      | ~ v1_relat_1(k2_funct_1(A_139))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_12])).

tff(c_633,plain,(
    ! [A_139] :
      ( r1_tarski(k2_relat_1(A_139),k1_relat_1(k2_funct_1(A_139)))
      | ~ v2_funct_1(A_139)
      | ~ v1_funct_1(A_139)
      | ~ v1_relat_1(A_139)
      | ~ v1_relat_1(k2_funct_1(A_139)) ) ),
    inference(resolution,[status(thm)],[c_232,c_606])).

tff(c_6564,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6559,c_633])).

tff(c_6574,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_4')))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_104,c_4279,c_6564])).

tff(c_6605,plain,(
    r1_tarski('#skF_1',k1_relat_1(k2_funct_1('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_6574])).

tff(c_209,plain,(
    ! [B_90,A_91] :
      ( r1_tarski(k1_relat_1(B_90),A_91)
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_215,plain,(
    ! [B_90,A_91] :
      ( k1_relat_1(B_90) = A_91
      | ~ r1_tarski(A_91,k1_relat_1(B_90))
      | ~ v4_relat_1(B_90,A_91)
      | ~ v1_relat_1(B_90) ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_6608,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1'
    | ~ v4_relat_1(k2_funct_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6605,c_215])).

tff(c_6616,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_6592,c_6608])).

tff(c_6560,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6559,c_326])).

tff(c_7849,plain,(
    ! [A_584,C_585,B_586] :
      ( k6_partfun1(A_584) = k5_relat_1(C_585,k2_funct_1(C_585))
      | k1_xboole_0 = B_586
      | ~ v2_funct_1(C_585)
      | k2_relset_1(A_584,B_586,C_585) != B_586
      | ~ m1_subset_1(C_585,k1_zfmisc_1(k2_zfmisc_1(A_584,B_586)))
      | ~ v1_funct_2(C_585,A_584,B_586)
      | ~ v1_funct_1(C_585) ) ),
    inference(cnfTransformation,[status(thm)],[f_252])).

tff(c_7857,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_7849])).

tff(c_7868,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_102,c_6560,c_4279,c_7857])).

tff(c_7869,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_7868])).

tff(c_32,plain,(
    ! [A_16,B_18] :
      ( v2_funct_1(A_16)
      | k2_relat_1(B_18) != k1_relat_1(A_16)
      | ~ v2_funct_1(k5_relat_1(B_18,A_16))
      | ~ v1_funct_1(B_18)
      | ~ v1_relat_1(B_18)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_7910,plain,
    ( v2_funct_1(k2_funct_1('#skF_4'))
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7869,c_32])).

tff(c_7925,plain,(
    v2_funct_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_6558,c_179,c_104,c_113,c_6559,c_6616,c_7910])).

tff(c_18,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_115,plain,(
    ! [A_13] : k1_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_18])).

tff(c_44,plain,(
    ! [A_21] :
      ( k1_relat_1(k5_relat_1(A_21,k2_funct_1(A_21))) = k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_7913,plain,
    ( k1_relat_1(k6_partfun1('#skF_2')) = k1_relat_1('#skF_4')
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7869,c_44])).

tff(c_7927,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_104,c_4279,c_115,c_7913])).

tff(c_38,plain,(
    ! [A_20] :
      ( k2_relat_1(k2_funct_1(A_20)) = k1_relat_1(A_20)
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_46,plain,(
    ! [A_22,B_24] :
      ( k2_funct_1(A_22) = B_24
      | k6_relat_1(k2_relat_1(A_22)) != k5_relat_1(B_24,A_22)
      | k2_relat_1(B_24) != k1_relat_1(A_22)
      | ~ v2_funct_1(A_22)
      | ~ v1_funct_1(B_24)
      | ~ v1_relat_1(B_24)
      | ~ v1_funct_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6620,plain,(
    ! [A_503,B_504] :
      ( k2_funct_1(A_503) = B_504
      | k6_partfun1(k2_relat_1(A_503)) != k5_relat_1(B_504,A_503)
      | k2_relat_1(B_504) != k1_relat_1(A_503)
      | ~ v2_funct_1(A_503)
      | ~ v1_funct_1(B_504)
      | ~ v1_relat_1(B_504)
      | ~ v1_funct_1(A_503)
      | ~ v1_relat_1(A_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_46])).

tff(c_12309,plain,(
    ! [A_758,B_759] :
      ( k2_funct_1(k2_funct_1(A_758)) = B_759
      | k5_relat_1(B_759,k2_funct_1(A_758)) != k6_partfun1(k1_relat_1(A_758))
      | k2_relat_1(B_759) != k1_relat_1(k2_funct_1(A_758))
      | ~ v2_funct_1(k2_funct_1(A_758))
      | ~ v1_funct_1(B_759)
      | ~ v1_relat_1(B_759)
      | ~ v1_funct_1(k2_funct_1(A_758))
      | ~ v1_relat_1(k2_funct_1(A_758))
      | ~ v2_funct_1(A_758)
      | ~ v1_funct_1(A_758)
      | ~ v1_relat_1(A_758) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6620])).

tff(c_12311,plain,
    ( k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4'
    | k6_partfun1(k1_relat_1('#skF_4')) != k6_partfun1('#skF_2')
    | k1_relat_1(k2_funct_1('#skF_4')) != k2_relat_1('#skF_4')
    | ~ v2_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_funct_1(k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7869,c_12309])).

tff(c_12315,plain,(
    k2_funct_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_104,c_4279,c_6593,c_6558,c_179,c_104,c_7925,c_6559,c_6616,c_7927,c_12311])).

tff(c_6628,plain,(
    ! [A_20,B_504] :
      ( k2_funct_1(k2_funct_1(A_20)) = B_504
      | k5_relat_1(B_504,k2_funct_1(A_20)) != k6_partfun1(k1_relat_1(A_20))
      | k2_relat_1(B_504) != k1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(k2_funct_1(A_20))
      | ~ v1_funct_1(B_504)
      | ~ v1_relat_1(B_504)
      | ~ v1_funct_1(k2_funct_1(A_20))
      | ~ v1_relat_1(k2_funct_1(A_20))
      | ~ v2_funct_1(A_20)
      | ~ v1_funct_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6620])).

tff(c_12335,plain,(
    ! [B_504] :
      ( k2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) = B_504
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_504,'#skF_4')
      | k2_relat_1(B_504) != k1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_504)
      | ~ v1_relat_1(B_504)
      | ~ v1_funct_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_funct_1(k2_funct_1('#skF_4'))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12315,c_6628])).

tff(c_12788,plain,(
    ! [B_772] :
      ( k2_funct_1('#skF_4') = B_772
      | k5_relat_1(B_772,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_772) != '#skF_2'
      | ~ v1_funct_1(B_772)
      | ~ v1_relat_1(B_772) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6593,c_6558,c_7925,c_179,c_12315,c_104,c_12315,c_4279,c_12315,c_7927,c_12315,c_6616,c_12315,c_12335])).

tff(c_12890,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_12788])).

tff(c_12994,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_325,c_7950,c_12890])).

tff(c_12998,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12994,c_12315])).

tff(c_13019,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_88,c_12998])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:19:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.38/4.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.24  
% 10.38/4.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.38/4.24  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.38/4.24  
% 10.38/4.24  %Foreground sorts:
% 10.38/4.24  
% 10.38/4.24  
% 10.38/4.24  %Background operators:
% 10.38/4.24  
% 10.38/4.24  
% 10.38/4.24  %Foreground operators:
% 10.38/4.24  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.38/4.24  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.38/4.24  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.38/4.24  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.38/4.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.38/4.24  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.38/4.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.38/4.24  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.38/4.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.38/4.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.38/4.24  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.38/4.24  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.38/4.24  tff('#skF_2', type, '#skF_2': $i).
% 10.38/4.24  tff('#skF_3', type, '#skF_3': $i).
% 10.38/4.24  tff('#skF_1', type, '#skF_1': $i).
% 10.38/4.24  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.38/4.24  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.38/4.24  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.38/4.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.38/4.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.38/4.24  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.38/4.24  tff('#skF_4', type, '#skF_4': $i).
% 10.38/4.24  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.38/4.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.38/4.24  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.38/4.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.38/4.24  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.38/4.24  
% 10.57/4.27  tff(f_278, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.57/4.27  tff(f_143, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.57/4.27  tff(f_165, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.57/4.27  tff(f_177, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.57/4.27  tff(f_153, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 10.57/4.27  tff(f_151, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.57/4.27  tff(f_175, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.57/4.27  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 10.57/4.27  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 10.57/4.27  tff(f_65, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.57/4.27  tff(f_236, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_funct_2)).
% 10.57/4.27  tff(f_96, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 10.57/4.27  tff(f_220, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 10.57/4.27  tff(f_194, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 10.57/4.27  tff(f_106, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 10.57/4.27  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.57/4.27  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 10.57/4.27  tff(f_252, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 10.57/4.27  tff(f_94, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & (k2_relat_1(B) = k1_relat_1(A))) => (v2_funct_1(B) & v2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_funct_1)).
% 10.57/4.27  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 10.57/4.27  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k1_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)) & (k2_relat_1(k5_relat_1(A, k2_funct_1(A))) = k1_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t58_funct_1)).
% 10.57/4.27  tff(f_133, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 10.57/4.27  tff(c_88, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_110, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_98, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_106, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_312, plain, (![A_110, B_111, C_112]: (k2_relset_1(A_110, B_111, C_112)=k2_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_143])).
% 10.57/4.27  tff(c_318, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_312])).
% 10.57/4.27  tff(c_325, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_98, c_318])).
% 10.57/4.27  tff(c_104, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_100, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_1791, plain, (![B_222, D_221, F_219, E_224, A_220, C_223]: (m1_subset_1(k1_partfun1(A_220, B_222, C_223, D_221, E_224, F_219), k1_zfmisc_1(k2_zfmisc_1(A_220, D_221))) | ~m1_subset_1(F_219, k1_zfmisc_1(k2_zfmisc_1(C_223, D_221))) | ~v1_funct_1(F_219) | ~m1_subset_1(E_224, k1_zfmisc_1(k2_zfmisc_1(A_220, B_222))) | ~v1_funct_1(E_224))), inference(cnfTransformation, [status(thm)], [f_165])).
% 10.57/4.27  tff(c_66, plain, (![A_48]: (k6_relat_1(A_48)=k6_partfun1(A_48))), inference(cnfTransformation, [status(thm)], [f_177])).
% 10.57/4.27  tff(c_58, plain, (![A_35]: (m1_subset_1(k6_relat_1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(cnfTransformation, [status(thm)], [f_153])).
% 10.57/4.27  tff(c_111, plain, (![A_35]: (m1_subset_1(k6_partfun1(A_35), k1_zfmisc_1(k2_zfmisc_1(A_35, A_35))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_58])).
% 10.57/4.27  tff(c_96, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_662, plain, (![D_142, C_143, A_144, B_145]: (D_142=C_143 | ~r2_relset_1(A_144, B_145, C_143, D_142) | ~m1_subset_1(D_142, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.57/4.27  tff(c_670, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_96, c_662])).
% 10.57/4.27  tff(c_685, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_670])).
% 10.57/4.27  tff(c_768, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_685])).
% 10.57/4.27  tff(c_1823, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1791, c_768])).
% 10.57/4.27  tff(c_1861, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_106, c_104, c_100, c_1823])).
% 10.57/4.27  tff(c_1862, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_685])).
% 10.57/4.27  tff(c_7635, plain, (![F_571, B_569, C_572, D_568, A_570, E_567]: (k1_partfun1(A_570, B_569, C_572, D_568, E_567, F_571)=k5_relat_1(E_567, F_571) | ~m1_subset_1(F_571, k1_zfmisc_1(k2_zfmisc_1(C_572, D_568))) | ~v1_funct_1(F_571) | ~m1_subset_1(E_567, k1_zfmisc_1(k2_zfmisc_1(A_570, B_569))) | ~v1_funct_1(E_567))), inference(cnfTransformation, [status(thm)], [f_175])).
% 10.57/4.27  tff(c_7641, plain, (![A_570, B_569, E_567]: (k1_partfun1(A_570, B_569, '#skF_2', '#skF_1', E_567, '#skF_4')=k5_relat_1(E_567, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_567, k1_zfmisc_1(k2_zfmisc_1(A_570, B_569))) | ~v1_funct_1(E_567))), inference(resolution, [status(thm)], [c_100, c_7635])).
% 10.57/4.27  tff(c_7933, plain, (![A_587, B_588, E_589]: (k1_partfun1(A_587, B_588, '#skF_2', '#skF_1', E_589, '#skF_4')=k5_relat_1(E_589, '#skF_4') | ~m1_subset_1(E_589, k1_zfmisc_1(k2_zfmisc_1(A_587, B_588))) | ~v1_funct_1(E_589))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_7641])).
% 10.57/4.27  tff(c_7942, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_106, c_7933])).
% 10.57/4.27  tff(c_7950, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_1862, c_7942])).
% 10.57/4.27  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 10.57/4.27  tff(c_161, plain, (![B_79, A_80]: (v1_relat_1(B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_80)) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_38])).
% 10.57/4.27  tff(c_167, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_106, c_161])).
% 10.57/4.27  tff(c_176, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_167])).
% 10.57/4.27  tff(c_170, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_100, c_161])).
% 10.57/4.27  tff(c_179, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_170])).
% 10.57/4.27  tff(c_24, plain, (![A_14]: (v1_relat_1(k2_funct_1(A_14)) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.57/4.27  tff(c_102, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_326, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_312])).
% 10.57/4.27  tff(c_2041, plain, (![C_233, A_234, B_235]: (v1_funct_1(k2_funct_1(C_233)) | k2_relset_1(A_234, B_235, C_233)!=B_235 | ~v2_funct_1(C_233) | ~m1_subset_1(C_233, k1_zfmisc_1(k2_zfmisc_1(A_234, B_235))) | ~v1_funct_2(C_233, A_234, B_235) | ~v1_funct_1(C_233))), inference(cnfTransformation, [status(thm)], [f_236])).
% 10.57/4.27  tff(c_2050, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_2041])).
% 10.57/4.27  tff(c_2059, plain, (v1_funct_1(k2_funct_1('#skF_4')) | k2_relat_1('#skF_4')!='#skF_1' | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_326, c_2050])).
% 10.57/4.27  tff(c_2068, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_2059])).
% 10.57/4.27  tff(c_92, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_108, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_278])).
% 10.57/4.27  tff(c_36, plain, (![A_19]: (v2_funct_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 10.57/4.27  tff(c_113, plain, (![A_19]: (v2_funct_1(k6_partfun1(A_19)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_36])).
% 10.57/4.27  tff(c_4261, plain, (![B_363, C_361, E_365, A_362, D_364]: (k1_xboole_0=C_361 | v2_funct_1(E_365) | k2_relset_1(A_362, B_363, D_364)!=B_363 | ~v2_funct_1(k1_partfun1(A_362, B_363, B_363, C_361, D_364, E_365)) | ~m1_subset_1(E_365, k1_zfmisc_1(k2_zfmisc_1(B_363, C_361))) | ~v1_funct_2(E_365, B_363, C_361) | ~v1_funct_1(E_365) | ~m1_subset_1(D_364, k1_zfmisc_1(k2_zfmisc_1(A_362, B_363))) | ~v1_funct_2(D_364, A_362, B_363) | ~v1_funct_1(D_364))), inference(cnfTransformation, [status(thm)], [f_220])).
% 10.57/4.27  tff(c_4267, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_4261])).
% 10.57/4.27  tff(c_4275, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_110, c_108, c_106, c_104, c_102, c_100, c_113, c_98, c_4267])).
% 10.57/4.27  tff(c_4277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2068, c_92, c_4275])).
% 10.57/4.27  tff(c_4279, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_2059])).
% 10.57/4.27  tff(c_4278, plain, (k2_relat_1('#skF_4')!='#skF_1' | v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_2059])).
% 10.57/4.27  tff(c_4280, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_4278])).
% 10.57/4.27  tff(c_267, plain, (![A_101, B_102, D_103]: (r2_relset_1(A_101, B_102, D_103, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_151])).
% 10.57/4.27  tff(c_274, plain, (![A_35]: (r2_relset_1(A_35, A_35, k6_partfun1(A_35), k6_partfun1(A_35)))), inference(resolution, [status(thm)], [c_111, c_267])).
% 10.57/4.27  tff(c_6545, plain, (![A_498, B_499, C_500, D_501]: (k2_relset_1(A_498, B_499, C_500)=B_499 | ~r2_relset_1(B_499, B_499, k1_partfun1(B_499, A_498, A_498, B_499, D_501, C_500), k6_partfun1(B_499)) | ~m1_subset_1(D_501, k1_zfmisc_1(k2_zfmisc_1(B_499, A_498))) | ~v1_funct_2(D_501, B_499, A_498) | ~v1_funct_1(D_501) | ~m1_subset_1(C_500, k1_zfmisc_1(k2_zfmisc_1(A_498, B_499))) | ~v1_funct_2(C_500, A_498, B_499) | ~v1_funct_1(C_500))), inference(cnfTransformation, [status(thm)], [f_194])).
% 10.57/4.27  tff(c_6551, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1862, c_6545])).
% 10.57/4.27  tff(c_6555, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_100, c_110, c_108, c_106, c_274, c_326, c_6551])).
% 10.57/4.27  tff(c_6557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4280, c_6555])).
% 10.57/4.27  tff(c_6559, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_4278])).
% 10.57/4.27  tff(c_294, plain, (![A_109]: (k1_relat_1(k2_funct_1(A_109))=k2_relat_1(A_109) | ~v2_funct_1(A_109) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.27  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.57/4.27  tff(c_218, plain, (![B_92, A_93]: (v4_relat_1(B_92, A_93) | ~r1_tarski(k1_relat_1(B_92), A_93) | ~v1_relat_1(B_92))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.57/4.27  tff(c_232, plain, (![B_92]: (v4_relat_1(B_92, k1_relat_1(B_92)) | ~v1_relat_1(B_92))), inference(resolution, [status(thm)], [c_6, c_218])).
% 10.57/4.27  tff(c_300, plain, (![A_109]: (v4_relat_1(k2_funct_1(A_109), k2_relat_1(A_109)) | ~v1_relat_1(k2_funct_1(A_109)) | ~v2_funct_1(A_109) | ~v1_funct_1(A_109) | ~v1_relat_1(A_109))), inference(superposition, [status(thm), theory('equality')], [c_294, c_232])).
% 10.57/4.27  tff(c_6567, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6559, c_300])).
% 10.57/4.27  tff(c_6576, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_104, c_4279, c_6567])).
% 10.57/4.27  tff(c_6584, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6576])).
% 10.57/4.27  tff(c_6587, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_6584])).
% 10.57/4.27  tff(c_6591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_104, c_6587])).
% 10.57/4.27  tff(c_6593, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6576])).
% 10.57/4.27  tff(c_6558, plain, (v1_funct_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4278])).
% 10.57/4.27  tff(c_6592, plain, (v4_relat_1(k2_funct_1('#skF_4'), '#skF_1')), inference(splitRight, [status(thm)], [c_6576])).
% 10.57/4.27  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k1_relat_1(B_7), A_6) | ~v4_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.57/4.27  tff(c_606, plain, (![A_139, A_140]: (r1_tarski(k2_relat_1(A_139), A_140) | ~v4_relat_1(k2_funct_1(A_139), A_140) | ~v1_relat_1(k2_funct_1(A_139)) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139))), inference(superposition, [status(thm), theory('equality')], [c_294, c_12])).
% 10.57/4.27  tff(c_633, plain, (![A_139]: (r1_tarski(k2_relat_1(A_139), k1_relat_1(k2_funct_1(A_139))) | ~v2_funct_1(A_139) | ~v1_funct_1(A_139) | ~v1_relat_1(A_139) | ~v1_relat_1(k2_funct_1(A_139)))), inference(resolution, [status(thm)], [c_232, c_606])).
% 10.57/4.27  tff(c_6564, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6559, c_633])).
% 10.57/4.27  tff(c_6574, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_104, c_4279, c_6564])).
% 10.57/4.27  tff(c_6605, plain, (r1_tarski('#skF_1', k1_relat_1(k2_funct_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_6574])).
% 10.57/4.27  tff(c_209, plain, (![B_90, A_91]: (r1_tarski(k1_relat_1(B_90), A_91) | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(cnfTransformation, [status(thm)], [f_44])).
% 10.57/4.27  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.57/4.27  tff(c_215, plain, (![B_90, A_91]: (k1_relat_1(B_90)=A_91 | ~r1_tarski(A_91, k1_relat_1(B_90)) | ~v4_relat_1(B_90, A_91) | ~v1_relat_1(B_90))), inference(resolution, [status(thm)], [c_209, c_2])).
% 10.57/4.27  tff(c_6608, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1' | ~v4_relat_1(k2_funct_1('#skF_4'), '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6605, c_215])).
% 10.57/4.27  tff(c_6616, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_6592, c_6608])).
% 10.57/4.27  tff(c_6560, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6559, c_326])).
% 10.57/4.27  tff(c_7849, plain, (![A_584, C_585, B_586]: (k6_partfun1(A_584)=k5_relat_1(C_585, k2_funct_1(C_585)) | k1_xboole_0=B_586 | ~v2_funct_1(C_585) | k2_relset_1(A_584, B_586, C_585)!=B_586 | ~m1_subset_1(C_585, k1_zfmisc_1(k2_zfmisc_1(A_584, B_586))) | ~v1_funct_2(C_585, A_584, B_586) | ~v1_funct_1(C_585))), inference(cnfTransformation, [status(thm)], [f_252])).
% 10.57/4.27  tff(c_7857, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_7849])).
% 10.57/4.27  tff(c_7868, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_102, c_6560, c_4279, c_7857])).
% 10.57/4.27  tff(c_7869, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_92, c_7868])).
% 10.57/4.27  tff(c_32, plain, (![A_16, B_18]: (v2_funct_1(A_16) | k2_relat_1(B_18)!=k1_relat_1(A_16) | ~v2_funct_1(k5_relat_1(B_18, A_16)) | ~v1_funct_1(B_18) | ~v1_relat_1(B_18) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_94])).
% 10.57/4.27  tff(c_7910, plain, (v2_funct_1(k2_funct_1('#skF_4')) | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7869, c_32])).
% 10.57/4.27  tff(c_7925, plain, (v2_funct_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_6558, c_179, c_104, c_113, c_6559, c_6616, c_7910])).
% 10.57/4.27  tff(c_18, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.57/4.27  tff(c_115, plain, (![A_13]: (k1_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_18])).
% 10.57/4.27  tff(c_44, plain, (![A_21]: (k1_relat_1(k5_relat_1(A_21, k2_funct_1(A_21)))=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_116])).
% 10.57/4.27  tff(c_7913, plain, (k1_relat_1(k6_partfun1('#skF_2'))=k1_relat_1('#skF_4') | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7869, c_44])).
% 10.57/4.27  tff(c_7927, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_104, c_4279, c_115, c_7913])).
% 10.57/4.27  tff(c_38, plain, (![A_20]: (k2_relat_1(k2_funct_1(A_20))=k1_relat_1(A_20) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_106])).
% 10.57/4.27  tff(c_46, plain, (![A_22, B_24]: (k2_funct_1(A_22)=B_24 | k6_relat_1(k2_relat_1(A_22))!=k5_relat_1(B_24, A_22) | k2_relat_1(B_24)!=k1_relat_1(A_22) | ~v2_funct_1(A_22) | ~v1_funct_1(B_24) | ~v1_relat_1(B_24) | ~v1_funct_1(A_22) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_133])).
% 10.57/4.27  tff(c_6620, plain, (![A_503, B_504]: (k2_funct_1(A_503)=B_504 | k6_partfun1(k2_relat_1(A_503))!=k5_relat_1(B_504, A_503) | k2_relat_1(B_504)!=k1_relat_1(A_503) | ~v2_funct_1(A_503) | ~v1_funct_1(B_504) | ~v1_relat_1(B_504) | ~v1_funct_1(A_503) | ~v1_relat_1(A_503))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_46])).
% 10.57/4.27  tff(c_12309, plain, (![A_758, B_759]: (k2_funct_1(k2_funct_1(A_758))=B_759 | k5_relat_1(B_759, k2_funct_1(A_758))!=k6_partfun1(k1_relat_1(A_758)) | k2_relat_1(B_759)!=k1_relat_1(k2_funct_1(A_758)) | ~v2_funct_1(k2_funct_1(A_758)) | ~v1_funct_1(B_759) | ~v1_relat_1(B_759) | ~v1_funct_1(k2_funct_1(A_758)) | ~v1_relat_1(k2_funct_1(A_758)) | ~v2_funct_1(A_758) | ~v1_funct_1(A_758) | ~v1_relat_1(A_758))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6620])).
% 10.57/4.27  tff(c_12311, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4' | k6_partfun1(k1_relat_1('#skF_4'))!=k6_partfun1('#skF_2') | k1_relat_1(k2_funct_1('#skF_4'))!=k2_relat_1('#skF_4') | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4') | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7869, c_12309])).
% 10.57/4.27  tff(c_12315, plain, (k2_funct_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_104, c_4279, c_6593, c_6558, c_179, c_104, c_7925, c_6559, c_6616, c_7927, c_12311])).
% 10.57/4.27  tff(c_6628, plain, (![A_20, B_504]: (k2_funct_1(k2_funct_1(A_20))=B_504 | k5_relat_1(B_504, k2_funct_1(A_20))!=k6_partfun1(k1_relat_1(A_20)) | k2_relat_1(B_504)!=k1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(k2_funct_1(A_20)) | ~v1_funct_1(B_504) | ~v1_relat_1(B_504) | ~v1_funct_1(k2_funct_1(A_20)) | ~v1_relat_1(k2_funct_1(A_20)) | ~v2_funct_1(A_20) | ~v1_funct_1(A_20) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6620])).
% 10.57/4.27  tff(c_12335, plain, (![B_504]: (k2_funct_1(k2_funct_1(k2_funct_1('#skF_4')))=B_504 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_504, '#skF_4') | k2_relat_1(B_504)!=k1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_504) | ~v1_relat_1(B_504) | ~v1_funct_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k2_funct_1('#skF_4')) | ~v1_funct_1(k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_12315, c_6628])).
% 10.57/4.27  tff(c_12788, plain, (![B_772]: (k2_funct_1('#skF_4')=B_772 | k5_relat_1(B_772, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_772)!='#skF_2' | ~v1_funct_1(B_772) | ~v1_relat_1(B_772))), inference(demodulation, [status(thm), theory('equality')], [c_6593, c_6558, c_7925, c_179, c_12315, c_104, c_12315, c_4279, c_12315, c_7927, c_12315, c_6616, c_12315, c_12335])).
% 10.57/4.27  tff(c_12890, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_176, c_12788])).
% 10.57/4.27  tff(c_12994, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_325, c_7950, c_12890])).
% 10.57/4.27  tff(c_12998, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12994, c_12315])).
% 10.57/4.27  tff(c_13019, plain, $false, inference(negUnitSimplification, [status(thm)], [c_88, c_12998])).
% 10.57/4.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.57/4.27  
% 10.57/4.27  Inference rules
% 10.57/4.27  ----------------------
% 10.57/4.27  #Ref     : 0
% 10.57/4.27  #Sup     : 2575
% 10.57/4.27  #Fact    : 0
% 10.57/4.27  #Define  : 0
% 10.57/4.27  #Split   : 68
% 10.57/4.27  #Chain   : 0
% 10.57/4.27  #Close   : 0
% 10.57/4.27  
% 10.57/4.27  Ordering : KBO
% 10.57/4.27  
% 10.57/4.27  Simplification rules
% 10.57/4.27  ----------------------
% 10.57/4.27  #Subsume      : 289
% 10.57/4.27  #Demod        : 4955
% 10.57/4.27  #Tautology    : 873
% 10.57/4.27  #SimpNegUnit  : 134
% 10.57/4.27  #BackRed      : 99
% 10.57/4.27  
% 10.57/4.27  #Partial instantiations: 0
% 10.57/4.27  #Strategies tried      : 1
% 10.57/4.27  
% 10.57/4.27  Timing (in seconds)
% 10.57/4.27  ----------------------
% 10.57/4.27  Preprocessing        : 0.41
% 10.57/4.27  Parsing              : 0.21
% 10.57/4.27  CNF conversion       : 0.03
% 10.57/4.27  Main loop            : 3.09
% 10.57/4.27  Inferencing          : 0.92
% 10.57/4.27  Reduction            : 1.33
% 10.57/4.27  Demodulation         : 1.03
% 10.57/4.27  BG Simplification    : 0.08
% 10.57/4.27  Subsumption          : 0.57
% 10.57/4.27  Abstraction          : 0.10
% 10.57/4.27  MUC search           : 0.00
% 10.57/4.28  Cooper               : 0.00
% 10.57/4.28  Total                : 3.55
% 10.57/4.28  Index Insertion      : 0.00
% 10.57/4.28  Index Deletion       : 0.00
% 10.57/4.28  Index Matching       : 0.00
% 10.57/4.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
