%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:16 EST 2020

% Result     : Theorem 11.96s
% Output     : CNFRefutation 12.26s
% Verified   : 
% Statistics : Number of formulae       :  256 (7429 expanded)
%              Number of leaves         :   51 (2591 expanded)
%              Depth                    :   25
%              Number of atoms          :  613 (27618 expanded)
%              Number of equality atoms :  226 (9160 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_241,negated_conjecture,(
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

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_215,axiom,(
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

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_173,axiom,(
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

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(k2_relat_1(A),k1_relat_1(B))
           => k1_relat_1(k5_relat_1(A,B)) = k1_relat_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_relat_1)).

tff(f_116,axiom,(
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

tff(f_91,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_199,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_90,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_88,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_86,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_335,plain,(
    ! [A_88,B_89,C_90] :
      ( k2_relset_1(A_88,B_89,C_90) = k2_relat_1(C_90)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_347,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_335])).

tff(c_3810,plain,(
    ! [A_377,C_378,B_379] :
      ( k6_partfun1(A_377) = k5_relat_1(C_378,k2_funct_1(C_378))
      | k1_xboole_0 = B_379
      | ~ v2_funct_1(C_378)
      | k2_relset_1(A_377,B_379,C_378) != B_379
      | ~ m1_subset_1(C_378,k1_zfmisc_1(k2_zfmisc_1(A_377,B_379)))
      | ~ v1_funct_2(C_378,A_377,B_379)
      | ~ v1_funct_1(C_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_3814,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_3810])).

tff(c_3822,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_347,c_3814])).

tff(c_3823,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_3822])).

tff(c_3881,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3823])).

tff(c_96,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_94,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_92,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_54,plain,(
    ! [A_37] : m1_subset_1(k6_partfun1(A_37),k1_zfmisc_1(k2_zfmisc_1(A_37,A_37))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_274,plain,(
    ! [A_84,B_85,D_86] :
      ( r2_relset_1(A_84,B_85,D_86,D_86)
      | ~ m1_subset_1(D_86,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_281,plain,(
    ! [A_37] : r2_relset_1(A_37,A_37,k6_partfun1(A_37),k6_partfun1(A_37)) ),
    inference(resolution,[status(thm)],[c_54,c_274])).

tff(c_1855,plain,(
    ! [A_235,D_240,B_236,F_238,E_237,C_239] :
      ( k1_partfun1(A_235,B_236,C_239,D_240,E_237,F_238) = k5_relat_1(E_237,F_238)
      | ~ m1_subset_1(F_238,k1_zfmisc_1(k2_zfmisc_1(C_239,D_240)))
      | ~ v1_funct_1(F_238)
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_1859,plain,(
    ! [A_235,B_236,E_237] :
      ( k1_partfun1(A_235,B_236,'#skF_2','#skF_1',E_237,'#skF_4') = k5_relat_1(E_237,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_237,k1_zfmisc_1(k2_zfmisc_1(A_235,B_236)))
      | ~ v1_funct_1(E_237) ) ),
    inference(resolution,[status(thm)],[c_86,c_1855])).

tff(c_1869,plain,(
    ! [A_241,B_242,E_243] :
      ( k1_partfun1(A_241,B_242,'#skF_2','#skF_1',E_243,'#skF_4') = k5_relat_1(E_243,'#skF_4')
      | ~ m1_subset_1(E_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(E_243) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_1859])).

tff(c_1878,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_1869])).

tff(c_1885,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_1878])).

tff(c_82,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_712,plain,(
    ! [D_108,C_109,A_110,B_111] :
      ( D_108 = C_109
      | ~ r2_relset_1(A_110,B_111,C_109,D_108)
      | ~ m1_subset_1(D_108,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_720,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_82,c_712])).

tff(c_735,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_720])).

tff(c_800,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_735])).

tff(c_1892,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_800])).

tff(c_2062,plain,(
    ! [B_252,C_256,A_254,E_253,D_251,F_255] :
      ( m1_subset_1(k1_partfun1(A_254,B_252,C_256,D_251,E_253,F_255),k1_zfmisc_1(k2_zfmisc_1(A_254,D_251)))
      | ~ m1_subset_1(F_255,k1_zfmisc_1(k2_zfmisc_1(C_256,D_251)))
      | ~ v1_funct_1(F_255)
      | ~ m1_subset_1(E_253,k1_zfmisc_1(k2_zfmisc_1(A_254,B_252)))
      | ~ v1_funct_1(E_253) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_2090,plain,
    ( m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1885,c_2062])).

tff(c_2107,plain,(
    m1_subset_1(k5_relat_1('#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_92,c_90,c_86,c_2090])).

tff(c_2109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1892,c_2107])).

tff(c_2110,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_735])).

tff(c_4455,plain,(
    ! [A_406,B_407,C_408,D_409] :
      ( k2_relset_1(A_406,B_407,C_408) = B_407
      | ~ r2_relset_1(B_407,B_407,k1_partfun1(B_407,A_406,A_406,B_407,D_409,C_408),k6_partfun1(B_407))
      | ~ m1_subset_1(D_409,k1_zfmisc_1(k2_zfmisc_1(B_407,A_406)))
      | ~ v1_funct_2(D_409,B_407,A_406)
      | ~ v1_funct_1(D_409)
      | ~ m1_subset_1(C_408,k1_zfmisc_1(k2_zfmisc_1(A_406,B_407)))
      | ~ v1_funct_2(C_408,A_406,B_407)
      | ~ v1_funct_1(C_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_4458,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_4455])).

tff(c_4460,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_86,c_96,c_94,c_92,c_281,c_347,c_4458])).

tff(c_4462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3881,c_4460])).

tff(c_4464,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_3823])).

tff(c_58,plain,(
    ! [A_44] : k6_relat_1(A_44) = k6_partfun1(A_44) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_24,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_101,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_24])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_84,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_80,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_3816,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_3810])).

tff(c_3826,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_3816])).

tff(c_3827,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_3826])).

tff(c_10,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_226,plain,(
    ! [B_78,A_79] :
      ( v1_relat_1(B_78)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_79))
      | ~ v1_relat_1(A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_235,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_92,c_226])).

tff(c_244,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_235])).

tff(c_32,plain,(
    ! [A_17] :
      ( v1_relat_1(k2_funct_1(A_17))
      | ~ v1_funct_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_261,plain,(
    ! [A_83] :
      ( k4_relat_1(A_83) = k2_funct_1(A_83)
      | ~ v2_funct_1(A_83)
      | ~ v1_funct_1(A_83)
      | ~ v1_relat_1(A_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_267,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_261])).

tff(c_273,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_96,c_267])).

tff(c_18,plain,(
    ! [A_11] :
      ( k2_relat_1(k4_relat_1(A_11)) = k1_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_287,plain,
    ( k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_18])).

tff(c_297,plain,(
    k2_relat_1(k2_funct_1('#skF_3')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_287])).

tff(c_344,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_335])).

tff(c_349,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_344])).

tff(c_20,plain,(
    ! [A_11] :
      ( k1_relat_1(k4_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_290,plain,
    ( k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_20])).

tff(c_299,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_290])).

tff(c_350,plain,(
    k1_relat_1(k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_299])).

tff(c_14,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_363,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k2_relat_1(k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_14])).

tff(c_366,plain,
    ( k9_relat_1(k2_funct_1('#skF_3'),'#skF_2') = k1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_297,c_363])).

tff(c_386,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_366])).

tff(c_389,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_386])).

tff(c_393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_96,c_389])).

tff(c_395,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_366])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_526,plain,(
    ! [A_98,B_99] :
      ( k1_relat_1(k5_relat_1(A_98,B_99)) = k1_relat_1(A_98)
      | ~ r1_tarski(k2_relat_1(A_98),k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1(A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_532,plain,(
    ! [B_99] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_99)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_99))
      | ~ v1_relat_1(B_99)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_526])).

tff(c_576,plain,(
    ! [B_102] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_102)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_102))
      | ~ v1_relat_1(B_102) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_532])).

tff(c_582,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3')
    | ~ r1_tarski('#skF_2','#skF_2')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_576])).

tff(c_590,plain,(
    k1_relat_1(k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_6,c_582])).

tff(c_3831,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3827,c_590])).

tff(c_3834,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_3831])).

tff(c_74,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_232,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_86,c_226])).

tff(c_241,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_232])).

tff(c_40,plain,(
    ! [A_21,B_23] :
      ( k2_funct_1(A_21) = B_23
      | k6_relat_1(k2_relat_1(A_21)) != k5_relat_1(B_23,A_21)
      | k2_relat_1(B_23) != k1_relat_1(A_21)
      | ~ v2_funct_1(A_21)
      | ~ v1_funct_1(B_23)
      | ~ v1_relat_1(B_23)
      | ~ v1_funct_1(A_21)
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_3471,plain,(
    ! [A_351,B_352] :
      ( k2_funct_1(A_351) = B_352
      | k6_partfun1(k2_relat_1(A_351)) != k5_relat_1(B_352,A_351)
      | k2_relat_1(B_352) != k1_relat_1(A_351)
      | ~ v2_funct_1(A_351)
      | ~ v1_funct_1(B_352)
      | ~ v1_relat_1(B_352)
      | ~ v1_funct_1(A_351)
      | ~ v1_relat_1(A_351) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_40])).

tff(c_3473,plain,(
    ! [B_352] :
      ( k2_funct_1('#skF_3') = B_352
      | k5_relat_1(B_352,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_352) != k1_relat_1('#skF_3')
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1(B_352)
      | ~ v1_relat_1(B_352)
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_349,c_3471])).

tff(c_3486,plain,(
    ! [B_353] :
      ( k2_funct_1('#skF_3') = B_353
      | k5_relat_1(B_353,'#skF_3') != k6_partfun1('#skF_2')
      | k2_relat_1(B_353) != k1_relat_1('#skF_3')
      | ~ v1_funct_1(B_353)
      | ~ v1_relat_1(B_353) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_96,c_80,c_3473])).

tff(c_3501,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_241,c_3486])).

tff(c_3522,plain,
    ( k2_funct_1('#skF_3') = '#skF_4'
    | k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_3501])).

tff(c_3523,plain,
    ( k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2')
    | k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_3522])).

tff(c_3528,plain,(
    k2_relat_1('#skF_4') != k1_relat_1('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_3523])).

tff(c_3846,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3834,c_3528])).

tff(c_4490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4464,c_3846])).

tff(c_4491,plain,(
    k5_relat_1('#skF_4','#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_3523])).

tff(c_8003,plain,(
    ! [D_586,E_583,A_581,F_584,C_585,B_582] :
      ( k1_partfun1(A_581,B_582,C_585,D_586,E_583,F_584) = k5_relat_1(E_583,F_584)
      | ~ m1_subset_1(F_584,k1_zfmisc_1(k2_zfmisc_1(C_585,D_586)))
      | ~ v1_funct_1(F_584)
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_581,B_582)))
      | ~ v1_funct_1(E_583) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_8007,plain,(
    ! [A_581,B_582,E_583] :
      ( k1_partfun1(A_581,B_582,'#skF_2','#skF_1',E_583,'#skF_4') = k5_relat_1(E_583,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_583,k1_zfmisc_1(k2_zfmisc_1(A_581,B_582)))
      | ~ v1_funct_1(E_583) ) ),
    inference(resolution,[status(thm)],[c_86,c_8003])).

tff(c_9832,plain,(
    ! [A_664,B_665,E_666] :
      ( k1_partfun1(A_664,B_665,'#skF_2','#skF_1',E_666,'#skF_4') = k5_relat_1(E_666,'#skF_4')
      | ~ m1_subset_1(E_666,k1_zfmisc_1(k2_zfmisc_1(A_664,B_665)))
      | ~ v1_funct_1(E_666) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_8007])).

tff(c_9850,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_9832])).

tff(c_9864,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_2110,c_9850])).

tff(c_8063,plain,(
    ! [A_592,C_593,B_594] :
      ( k6_partfun1(A_592) = k5_relat_1(C_593,k2_funct_1(C_593))
      | k1_xboole_0 = B_594
      | ~ v2_funct_1(C_593)
      | k2_relset_1(A_592,B_594,C_593) != B_594
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_592,B_594)))
      | ~ v1_funct_2(C_593,A_592,B_594)
      | ~ v1_funct_1(C_593) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_8069,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_8063])).

tff(c_8079,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_8069])).

tff(c_8080,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_8079])).

tff(c_8084,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8080,c_590])).

tff(c_8086,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_8084])).

tff(c_4492,plain,(
    k2_relat_1('#skF_4') = k1_relat_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_3523])).

tff(c_4493,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4492,c_347])).

tff(c_8067,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_8063])).

tff(c_8075,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4493,c_8067])).

tff(c_8076,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8075])).

tff(c_8138,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8086,c_8076])).

tff(c_8139,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8138])).

tff(c_36,plain,(
    ! [A_18] : v2_funct_1(k6_relat_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_98,plain,(
    ! [A_18] : v2_funct_1(k6_partfun1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_36])).

tff(c_8582,plain,(
    ! [E_617,B_619,A_616,C_618,D_620] :
      ( k1_xboole_0 = C_618
      | v2_funct_1(E_617)
      | k2_relset_1(A_616,B_619,D_620) != B_619
      | ~ v2_funct_1(k1_partfun1(A_616,B_619,B_619,C_618,D_620,E_617))
      | ~ m1_subset_1(E_617,k1_zfmisc_1(k2_zfmisc_1(B_619,C_618)))
      | ~ v1_funct_2(E_617,B_619,C_618)
      | ~ v1_funct_1(E_617)
      | ~ m1_subset_1(D_620,k1_zfmisc_1(k2_zfmisc_1(A_616,B_619)))
      | ~ v1_funct_2(D_620,A_616,B_619)
      | ~ v1_funct_1(D_620) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_8586,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_8582])).

tff(c_8591,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_98,c_84,c_8586])).

tff(c_8593,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8139,c_78,c_8591])).

tff(c_8595,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8138])).

tff(c_28,plain,(
    ! [A_16] :
      ( k4_relat_1(A_16) = k2_funct_1(A_16)
      | ~ v2_funct_1(A_16)
      | ~ v1_funct_1(A_16)
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_8598,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8595,c_28])).

tff(c_8601,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_90,c_8598])).

tff(c_5566,plain,(
    ! [A_461,C_462,B_463] :
      ( k6_partfun1(A_461) = k5_relat_1(C_462,k2_funct_1(C_462))
      | k1_xboole_0 = B_463
      | ~ v2_funct_1(C_462)
      | k2_relset_1(A_461,B_463,C_462) != B_463
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_461,B_463)))
      | ~ v1_funct_2(C_462,A_461,B_463)
      | ~ v1_funct_1(C_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_5572,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_92,c_5566])).

tff(c_5582,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_84,c_80,c_5572])).

tff(c_5583,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_5582])).

tff(c_5587,plain,(
    k1_relat_1(k6_partfun1('#skF_1')) = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5583,c_590])).

tff(c_5589,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_5587])).

tff(c_5570,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_5566])).

tff(c_5578,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_88,c_4493,c_5570])).

tff(c_5579,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4')
    | k1_relat_1('#skF_3') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_5578])).

tff(c_5640,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5589,c_5579])).

tff(c_5641,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_5640])).

tff(c_6570,plain,(
    ! [C_507,B_508,A_505,D_509,E_506] :
      ( k1_xboole_0 = C_507
      | v2_funct_1(E_506)
      | k2_relset_1(A_505,B_508,D_509) != B_508
      | ~ v2_funct_1(k1_partfun1(A_505,B_508,B_508,C_507,D_509,E_506))
      | ~ m1_subset_1(E_506,k1_zfmisc_1(k2_zfmisc_1(B_508,C_507)))
      | ~ v1_funct_2(E_506,B_508,C_507)
      | ~ v1_funct_1(E_506)
      | ~ m1_subset_1(D_509,k1_zfmisc_1(k2_zfmisc_1(A_505,B_508)))
      | ~ v1_funct_2(D_509,A_505,B_508)
      | ~ v1_funct_1(D_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_6574,plain,
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
    inference(superposition,[status(thm),theory(equality)],[c_2110,c_6570])).

tff(c_6579,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_90,c_88,c_86,c_98,c_84,c_6574])).

tff(c_6581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5641,c_78,c_6579])).

tff(c_6583,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_5640])).

tff(c_6586,plain,
    ( k4_relat_1('#skF_4') = k2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6583,c_28])).

tff(c_6589,plain,(
    k4_relat_1('#skF_4') = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_90,c_6586])).

tff(c_183,plain,(
    ! [A_75] :
      ( k9_relat_1(A_75,k1_relat_1(A_75)) = k2_relat_1(A_75)
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_192,plain,(
    ! [A_11] :
      ( k9_relat_1(k4_relat_1(A_11),k2_relat_1(A_11)) = k2_relat_1(k4_relat_1(A_11))
      | ~ v1_relat_1(k4_relat_1(A_11))
      | ~ v1_relat_1(A_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_183])).

tff(c_4502,plain,
    ( k9_relat_1(k4_relat_1('#skF_4'),k1_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_4492,c_192])).

tff(c_4513,plain,
    ( k9_relat_1(k4_relat_1('#skF_4'),k1_relat_1('#skF_3')) = k2_relat_1(k4_relat_1('#skF_4'))
    | ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_4502])).

tff(c_4526,plain,(
    ~ v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_4513])).

tff(c_6663,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6589,c_4526])).

tff(c_6695,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_6663])).

tff(c_6699,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_90,c_6695])).

tff(c_6701,plain,(
    v1_relat_1(k4_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4513])).

tff(c_8694,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8601,c_6701])).

tff(c_12,plain,(
    ! [A_8] :
      ( k4_relat_1(k4_relat_1(A_8)) = A_8
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8710,plain,
    ( k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8601,c_12])).

tff(c_8722,plain,(
    k4_relat_1(k2_funct_1('#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_8710])).

tff(c_8594,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_8138])).

tff(c_8102,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8086,c_4492])).

tff(c_8707,plain,
    ( k1_relat_1(k2_funct_1('#skF_4')) = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8601,c_20])).

tff(c_8720,plain,(
    k1_relat_1(k2_funct_1('#skF_4')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_8102,c_8707])).

tff(c_22,plain,(
    ! [A_12,B_14] :
      ( k1_relat_1(k5_relat_1(A_12,B_14)) = k1_relat_1(A_12)
      | ~ r1_tarski(k2_relat_1(A_12),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8607,plain,(
    ! [B_14] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_14)) = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',k1_relat_1(B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8102,c_22])).

tff(c_9699,plain,(
    ! [B_663] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_663)) = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',k1_relat_1(B_663))
      | ~ v1_relat_1(B_663) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_8607])).

tff(c_9729,plain,
    ( k1_relat_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8720,c_9699])).

tff(c_9769,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8694,c_6,c_101,c_8594,c_9729])).

tff(c_4499,plain,(
    ! [B_14] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_14)) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4492,c_22])).

tff(c_4511,plain,(
    ! [B_14] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_14)) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_4499])).

tff(c_9484,plain,(
    ! [B_660] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_660)) = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',k1_relat_1(B_660))
      | ~ v1_relat_1(B_660) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8086,c_4511])).

tff(c_9508,plain,
    ( k1_relat_1(k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8720,c_9484])).

tff(c_9544,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8694,c_6,c_101,c_8594,c_9508])).

tff(c_6706,plain,(
    ! [B_513] :
      ( k1_relat_1(k5_relat_1('#skF_4',B_513)) = k1_relat_1('#skF_4')
      | ~ r1_tarski(k1_relat_1('#skF_3'),k1_relat_1(B_513))
      | ~ v1_relat_1(B_513) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_4499])).

tff(c_6755,plain,
    ( k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_6,c_6706])).

tff(c_6772,plain,(
    k1_relat_1(k5_relat_1('#skF_4','#skF_3')) = k1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_6755])).

tff(c_6791,plain,
    ( k9_relat_1(k5_relat_1('#skF_4','#skF_3'),k1_relat_1('#skF_4')) = k2_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6772,c_14])).

tff(c_6861,plain,(
    ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6791])).

tff(c_7085,plain,(
    ! [F_538,C_539,E_537,D_540,B_536,A_535] :
      ( k1_partfun1(A_535,B_536,C_539,D_540,E_537,F_538) = k5_relat_1(E_537,F_538)
      | ~ m1_subset_1(F_538,k1_zfmisc_1(k2_zfmisc_1(C_539,D_540)))
      | ~ v1_funct_1(F_538)
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(A_535,B_536)))
      | ~ v1_funct_1(E_537) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_7091,plain,(
    ! [A_535,B_536,E_537] :
      ( k1_partfun1(A_535,B_536,'#skF_1','#skF_2',E_537,'#skF_3') = k5_relat_1(E_537,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_537,k1_zfmisc_1(k2_zfmisc_1(A_535,B_536)))
      | ~ v1_funct_1(E_537) ) ),
    inference(resolution,[status(thm)],[c_92,c_7085])).

tff(c_7471,plain,(
    ! [A_560,B_561,E_562] :
      ( k1_partfun1(A_560,B_561,'#skF_1','#skF_2',E_562,'#skF_3') = k5_relat_1(E_562,'#skF_3')
      | ~ m1_subset_1(E_562,k1_zfmisc_1(k2_zfmisc_1(A_560,B_561)))
      | ~ v1_funct_1(E_562) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_7091])).

tff(c_7480,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_7471])).

tff(c_7488,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_7480])).

tff(c_48,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( m1_subset_1(k1_partfun1(A_31,B_32,C_33,D_34,E_35,F_36),k1_zfmisc_1(k2_zfmisc_1(A_31,D_34)))
      | ~ m1_subset_1(F_36,k1_zfmisc_1(k2_zfmisc_1(C_33,D_34)))
      | ~ v1_funct_1(F_36)
      | ~ m1_subset_1(E_35,k1_zfmisc_1(k2_zfmisc_1(A_31,B_32)))
      | ~ v1_funct_1(E_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_7756,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_7488,c_48])).

tff(c_7760,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_86,c_96,c_92,c_7756])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_7790,plain,
    ( v1_relat_1(k5_relat_1('#skF_4','#skF_3'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(resolution,[status(thm)],[c_7760,c_8])).

tff(c_7821,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_7790])).

tff(c_7823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6861,c_7821])).

tff(c_7825,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6791])).

tff(c_551,plain,(
    ! [B_99] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_99)) = k1_relat_1('#skF_3')
      | ~ r1_tarski('#skF_2',k1_relat_1(B_99))
      | ~ v1_relat_1(B_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_532])).

tff(c_9326,plain,(
    ! [B_658] :
      ( k1_relat_1(k5_relat_1('#skF_3',B_658)) = '#skF_1'
      | ~ r1_tarski('#skF_2',k1_relat_1(B_658))
      | ~ v1_relat_1(B_658) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8086,c_551])).

tff(c_9356,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k5_relat_1('#skF_4','#skF_3'))) = '#skF_1'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6772,c_9326])).

tff(c_9389,plain,
    ( k1_relat_1(k5_relat_1('#skF_3',k5_relat_1('#skF_4','#skF_3'))) = '#skF_1'
    | ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7825,c_9356])).

tff(c_9398,plain,(
    ~ r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_9389])).

tff(c_9556,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9544,c_9398])).

tff(c_9568,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9556])).

tff(c_9570,plain,(
    r1_tarski('#skF_2',k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_9389])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_9579,plain,
    ( k1_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_9570,c_2])).

tff(c_9613,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_9579])).

tff(c_9781,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9769,c_9613])).

tff(c_9794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_9781])).

tff(c_9795,plain,(
    k1_relat_1('#skF_4') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9579])).

tff(c_11354,plain,(
    ! [A_706,B_707] :
      ( k2_funct_1(k4_relat_1(A_706)) = B_707
      | k5_relat_1(B_707,k4_relat_1(A_706)) != k6_partfun1(k1_relat_1(A_706))
      | k2_relat_1(B_707) != k1_relat_1(k4_relat_1(A_706))
      | ~ v2_funct_1(k4_relat_1(A_706))
      | ~ v1_funct_1(B_707)
      | ~ v1_relat_1(B_707)
      | ~ v1_funct_1(k4_relat_1(A_706))
      | ~ v1_relat_1(k4_relat_1(A_706))
      | ~ v1_relat_1(A_706) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_3471])).

tff(c_11356,plain,(
    ! [B_707] :
      ( k2_funct_1(k4_relat_1(k2_funct_1('#skF_4'))) = B_707
      | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4'))) != k5_relat_1(B_707,'#skF_4')
      | k2_relat_1(B_707) != k1_relat_1(k4_relat_1(k2_funct_1('#skF_4')))
      | ~ v2_funct_1(k4_relat_1(k2_funct_1('#skF_4')))
      | ~ v1_funct_1(B_707)
      | ~ v1_relat_1(B_707)
      | ~ v1_funct_1(k4_relat_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k4_relat_1(k2_funct_1('#skF_4')))
      | ~ v1_relat_1(k2_funct_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8722,c_11354])).

tff(c_19506,plain,(
    ! [B_883] :
      ( k2_funct_1('#skF_4') = B_883
      | k5_relat_1(B_883,'#skF_4') != k6_partfun1('#skF_1')
      | k2_relat_1(B_883) != '#skF_2'
      | ~ v1_funct_1(B_883)
      | ~ v1_relat_1(B_883) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8694,c_241,c_8722,c_90,c_8722,c_8595,c_8722,c_9795,c_8722,c_8720,c_8722,c_11356])).

tff(c_19650,plain,
    ( k2_funct_1('#skF_4') = '#skF_3'
    | k5_relat_1('#skF_3','#skF_4') != k6_partfun1('#skF_1')
    | k2_relat_1('#skF_3') != '#skF_2'
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_19506])).

tff(c_19783,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_349,c_9864,c_19650])).

tff(c_19799,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_19783,c_8594])).

tff(c_19809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4491,c_19799])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:58:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.96/5.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/5.30  
% 12.00/5.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.00/5.30  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k9_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k6_relat_1 > k6_partfun1 > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 12.00/5.30  
% 12.00/5.30  %Foreground sorts:
% 12.00/5.30  
% 12.00/5.30  
% 12.00/5.30  %Background operators:
% 12.00/5.30  
% 12.00/5.30  
% 12.00/5.30  %Foreground operators:
% 12.00/5.30  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 12.00/5.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 12.00/5.30  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 12.00/5.30  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 12.00/5.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.00/5.30  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 12.00/5.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.00/5.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 12.00/5.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.00/5.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 12.00/5.30  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.00/5.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 12.00/5.30  tff('#skF_2', type, '#skF_2': $i).
% 12.00/5.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.00/5.30  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 12.00/5.30  tff('#skF_3', type, '#skF_3': $i).
% 12.00/5.30  tff('#skF_1', type, '#skF_1': $i).
% 12.00/5.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 12.00/5.30  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 12.00/5.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.00/5.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 12.00/5.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.00/5.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 12.00/5.30  tff('#skF_4', type, '#skF_4': $i).
% 12.00/5.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 12.00/5.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.00/5.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 12.00/5.30  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 12.00/5.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 12.00/5.30  
% 12.26/5.33  tff(f_241, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 12.26/5.33  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 12.26/5.33  tff(f_215, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 12.26/5.33  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 12.26/5.33  tff(f_128, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 12.26/5.33  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 12.26/5.33  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 12.26/5.33  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 12.26/5.33  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 12.26/5.33  tff(f_71, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 12.26/5.33  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 12.26/5.33  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 12.26/5.33  tff(f_87, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 12.26/5.33  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d9_funct_1)).
% 12.26/5.33  tff(f_58, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t37_relat_1)).
% 12.26/5.33  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 12.26/5.33  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.26/5.33  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(A), k1_relat_1(B)) => (k1_relat_1(k5_relat_1(A, B)) = k1_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_relat_1)).
% 12.26/5.33  tff(f_116, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((v2_funct_1(A) & (k2_relat_1(B) = k1_relat_1(A))) & (k5_relat_1(B, A) = k6_relat_1(k2_relat_1(A)))) => (B = k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_funct_1)).
% 12.26/5.33  tff(f_91, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 12.26/5.33  tff(f_199, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 12.26/5.33  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 12.26/5.33  tff(c_78, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_90, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_88, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_86, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_335, plain, (![A_88, B_89, C_90]: (k2_relset_1(A_88, B_89, C_90)=k2_relat_1(C_90) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 12.26/5.33  tff(c_347, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_335])).
% 12.26/5.33  tff(c_3810, plain, (![A_377, C_378, B_379]: (k6_partfun1(A_377)=k5_relat_1(C_378, k2_funct_1(C_378)) | k1_xboole_0=B_379 | ~v2_funct_1(C_378) | k2_relset_1(A_377, B_379, C_378)!=B_379 | ~m1_subset_1(C_378, k1_zfmisc_1(k2_zfmisc_1(A_377, B_379))) | ~v1_funct_2(C_378, A_377, B_379) | ~v1_funct_1(C_378))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.26/5.33  tff(c_3814, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_3810])).
% 12.26/5.33  tff(c_3822, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_347, c_3814])).
% 12.26/5.33  tff(c_3823, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_78, c_3822])).
% 12.26/5.33  tff(c_3881, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_3823])).
% 12.26/5.33  tff(c_96, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_94, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_92, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_54, plain, (![A_37]: (m1_subset_1(k6_partfun1(A_37), k1_zfmisc_1(k2_zfmisc_1(A_37, A_37))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 12.26/5.33  tff(c_274, plain, (![A_84, B_85, D_86]: (r2_relset_1(A_84, B_85, D_86, D_86) | ~m1_subset_1(D_86, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.26/5.33  tff(c_281, plain, (![A_37]: (r2_relset_1(A_37, A_37, k6_partfun1(A_37), k6_partfun1(A_37)))), inference(resolution, [status(thm)], [c_54, c_274])).
% 12.26/5.33  tff(c_1855, plain, (![A_235, D_240, B_236, F_238, E_237, C_239]: (k1_partfun1(A_235, B_236, C_239, D_240, E_237, F_238)=k5_relat_1(E_237, F_238) | ~m1_subset_1(F_238, k1_zfmisc_1(k2_zfmisc_1(C_239, D_240))) | ~v1_funct_1(F_238) | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_1(E_237))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.26/5.33  tff(c_1859, plain, (![A_235, B_236, E_237]: (k1_partfun1(A_235, B_236, '#skF_2', '#skF_1', E_237, '#skF_4')=k5_relat_1(E_237, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_237, k1_zfmisc_1(k2_zfmisc_1(A_235, B_236))) | ~v1_funct_1(E_237))), inference(resolution, [status(thm)], [c_86, c_1855])).
% 12.26/5.33  tff(c_1869, plain, (![A_241, B_242, E_243]: (k1_partfun1(A_241, B_242, '#skF_2', '#skF_1', E_243, '#skF_4')=k5_relat_1(E_243, '#skF_4') | ~m1_subset_1(E_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~v1_funct_1(E_243))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_1859])).
% 12.26/5.33  tff(c_1878, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_1869])).
% 12.26/5.33  tff(c_1885, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_1878])).
% 12.26/5.33  tff(c_82, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_712, plain, (![D_108, C_109, A_110, B_111]: (D_108=C_109 | ~r2_relset_1(A_110, B_111, C_109, D_108) | ~m1_subset_1(D_108, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 12.26/5.33  tff(c_720, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_82, c_712])).
% 12.26/5.33  tff(c_735, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_720])).
% 12.26/5.33  tff(c_800, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_735])).
% 12.26/5.33  tff(c_1892, plain, (~m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1885, c_800])).
% 12.26/5.33  tff(c_2062, plain, (![B_252, C_256, A_254, E_253, D_251, F_255]: (m1_subset_1(k1_partfun1(A_254, B_252, C_256, D_251, E_253, F_255), k1_zfmisc_1(k2_zfmisc_1(A_254, D_251))) | ~m1_subset_1(F_255, k1_zfmisc_1(k2_zfmisc_1(C_256, D_251))) | ~v1_funct_1(F_255) | ~m1_subset_1(E_253, k1_zfmisc_1(k2_zfmisc_1(A_254, B_252))) | ~v1_funct_1(E_253))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.26/5.33  tff(c_2090, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1885, c_2062])).
% 12.26/5.33  tff(c_2107, plain, (m1_subset_1(k5_relat_1('#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_92, c_90, c_86, c_2090])).
% 12.26/5.33  tff(c_2109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1892, c_2107])).
% 12.26/5.33  tff(c_2110, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_735])).
% 12.26/5.33  tff(c_4455, plain, (![A_406, B_407, C_408, D_409]: (k2_relset_1(A_406, B_407, C_408)=B_407 | ~r2_relset_1(B_407, B_407, k1_partfun1(B_407, A_406, A_406, B_407, D_409, C_408), k6_partfun1(B_407)) | ~m1_subset_1(D_409, k1_zfmisc_1(k2_zfmisc_1(B_407, A_406))) | ~v1_funct_2(D_409, B_407, A_406) | ~v1_funct_1(D_409) | ~m1_subset_1(C_408, k1_zfmisc_1(k2_zfmisc_1(A_406, B_407))) | ~v1_funct_2(C_408, A_406, B_407) | ~v1_funct_1(C_408))), inference(cnfTransformation, [status(thm)], [f_173])).
% 12.26/5.33  tff(c_4458, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_4455])).
% 12.26/5.33  tff(c_4460, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_86, c_96, c_94, c_92, c_281, c_347, c_4458])).
% 12.26/5.33  tff(c_4462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3881, c_4460])).
% 12.26/5.33  tff(c_4464, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_3823])).
% 12.26/5.33  tff(c_58, plain, (![A_44]: (k6_relat_1(A_44)=k6_partfun1(A_44))), inference(cnfTransformation, [status(thm)], [f_156])).
% 12.26/5.33  tff(c_24, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_71])).
% 12.26/5.33  tff(c_101, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_58, c_24])).
% 12.26/5.33  tff(c_76, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_84, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_80, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_3816, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_3810])).
% 12.26/5.33  tff(c_3826, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_3816])).
% 12.26/5.33  tff(c_3827, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_3826])).
% 12.26/5.33  tff(c_10, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 12.26/5.33  tff(c_226, plain, (![B_78, A_79]: (v1_relat_1(B_78) | ~m1_subset_1(B_78, k1_zfmisc_1(A_79)) | ~v1_relat_1(A_79))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.26/5.33  tff(c_235, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_92, c_226])).
% 12.26/5.33  tff(c_244, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_235])).
% 12.26/5.33  tff(c_32, plain, (![A_17]: (v1_relat_1(k2_funct_1(A_17)) | ~v1_funct_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_87])).
% 12.26/5.33  tff(c_261, plain, (![A_83]: (k4_relat_1(A_83)=k2_funct_1(A_83) | ~v2_funct_1(A_83) | ~v1_funct_1(A_83) | ~v1_relat_1(A_83))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.26/5.33  tff(c_267, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_261])).
% 12.26/5.33  tff(c_273, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_96, c_267])).
% 12.26/5.33  tff(c_18, plain, (![A_11]: (k2_relat_1(k4_relat_1(A_11))=k1_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.26/5.33  tff(c_287, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_273, c_18])).
% 12.26/5.33  tff(c_297, plain, (k2_relat_1(k2_funct_1('#skF_3'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_287])).
% 12.26/5.33  tff(c_344, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_335])).
% 12.26/5.33  tff(c_349, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_344])).
% 12.26/5.33  tff(c_20, plain, (![A_11]: (k1_relat_1(k4_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_58])).
% 12.26/5.33  tff(c_290, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_273, c_20])).
% 12.26/5.33  tff(c_299, plain, (k1_relat_1(k2_funct_1('#skF_3'))=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_290])).
% 12.26/5.33  tff(c_350, plain, (k1_relat_1(k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_299])).
% 12.26/5.33  tff(c_14, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.26/5.33  tff(c_363, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k2_relat_1(k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_14])).
% 12.26/5.33  tff(c_366, plain, (k9_relat_1(k2_funct_1('#skF_3'), '#skF_2')=k1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_297, c_363])).
% 12.26/5.33  tff(c_386, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_366])).
% 12.26/5.33  tff(c_389, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_386])).
% 12.26/5.33  tff(c_393, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_244, c_96, c_389])).
% 12.26/5.33  tff(c_395, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_366])).
% 12.26/5.33  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.26/5.33  tff(c_526, plain, (![A_98, B_99]: (k1_relat_1(k5_relat_1(A_98, B_99))=k1_relat_1(A_98) | ~r1_tarski(k2_relat_1(A_98), k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1(A_98))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.26/5.33  tff(c_532, plain, (![B_99]: (k1_relat_1(k5_relat_1('#skF_3', B_99))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_99)) | ~v1_relat_1(B_99) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_349, c_526])).
% 12.26/5.33  tff(c_576, plain, (![B_102]: (k1_relat_1(k5_relat_1('#skF_3', B_102))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_102)) | ~v1_relat_1(B_102))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_532])).
% 12.26/5.33  tff(c_582, plain, (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', '#skF_2') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_350, c_576])).
% 12.26/5.33  tff(c_590, plain, (k1_relat_1(k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_395, c_6, c_582])).
% 12.26/5.33  tff(c_3831, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3827, c_590])).
% 12.26/5.33  tff(c_3834, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_3831])).
% 12.26/5.33  tff(c_74, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_241])).
% 12.26/5.33  tff(c_232, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_86, c_226])).
% 12.26/5.33  tff(c_241, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_232])).
% 12.26/5.33  tff(c_40, plain, (![A_21, B_23]: (k2_funct_1(A_21)=B_23 | k6_relat_1(k2_relat_1(A_21))!=k5_relat_1(B_23, A_21) | k2_relat_1(B_23)!=k1_relat_1(A_21) | ~v2_funct_1(A_21) | ~v1_funct_1(B_23) | ~v1_relat_1(B_23) | ~v1_funct_1(A_21) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_116])).
% 12.26/5.33  tff(c_3471, plain, (![A_351, B_352]: (k2_funct_1(A_351)=B_352 | k6_partfun1(k2_relat_1(A_351))!=k5_relat_1(B_352, A_351) | k2_relat_1(B_352)!=k1_relat_1(A_351) | ~v2_funct_1(A_351) | ~v1_funct_1(B_352) | ~v1_relat_1(B_352) | ~v1_funct_1(A_351) | ~v1_relat_1(A_351))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_40])).
% 12.26/5.33  tff(c_3473, plain, (![B_352]: (k2_funct_1('#skF_3')=B_352 | k5_relat_1(B_352, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_352)!=k1_relat_1('#skF_3') | ~v2_funct_1('#skF_3') | ~v1_funct_1(B_352) | ~v1_relat_1(B_352) | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_349, c_3471])).
% 12.26/5.33  tff(c_3486, plain, (![B_353]: (k2_funct_1('#skF_3')=B_353 | k5_relat_1(B_353, '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1(B_353)!=k1_relat_1('#skF_3') | ~v1_funct_1(B_353) | ~v1_relat_1(B_353))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_96, c_80, c_3473])).
% 12.26/5.33  tff(c_3501, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_241, c_3486])).
% 12.26/5.33  tff(c_3522, plain, (k2_funct_1('#skF_3')='#skF_4' | k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_3501])).
% 12.26/5.33  tff(c_3523, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2') | k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_74, c_3522])).
% 12.26/5.33  tff(c_3528, plain, (k2_relat_1('#skF_4')!=k1_relat_1('#skF_3')), inference(splitLeft, [status(thm)], [c_3523])).
% 12.26/5.33  tff(c_3846, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3834, c_3528])).
% 12.26/5.33  tff(c_4490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4464, c_3846])).
% 12.26/5.33  tff(c_4491, plain, (k5_relat_1('#skF_4', '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_3523])).
% 12.26/5.33  tff(c_8003, plain, (![D_586, E_583, A_581, F_584, C_585, B_582]: (k1_partfun1(A_581, B_582, C_585, D_586, E_583, F_584)=k5_relat_1(E_583, F_584) | ~m1_subset_1(F_584, k1_zfmisc_1(k2_zfmisc_1(C_585, D_586))) | ~v1_funct_1(F_584) | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_581, B_582))) | ~v1_funct_1(E_583))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.26/5.33  tff(c_8007, plain, (![A_581, B_582, E_583]: (k1_partfun1(A_581, B_582, '#skF_2', '#skF_1', E_583, '#skF_4')=k5_relat_1(E_583, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_583, k1_zfmisc_1(k2_zfmisc_1(A_581, B_582))) | ~v1_funct_1(E_583))), inference(resolution, [status(thm)], [c_86, c_8003])).
% 12.26/5.33  tff(c_9832, plain, (![A_664, B_665, E_666]: (k1_partfun1(A_664, B_665, '#skF_2', '#skF_1', E_666, '#skF_4')=k5_relat_1(E_666, '#skF_4') | ~m1_subset_1(E_666, k1_zfmisc_1(k2_zfmisc_1(A_664, B_665))) | ~v1_funct_1(E_666))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_8007])).
% 12.26/5.33  tff(c_9850, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_9832])).
% 12.26/5.33  tff(c_9864, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_2110, c_9850])).
% 12.26/5.33  tff(c_8063, plain, (![A_592, C_593, B_594]: (k6_partfun1(A_592)=k5_relat_1(C_593, k2_funct_1(C_593)) | k1_xboole_0=B_594 | ~v2_funct_1(C_593) | k2_relset_1(A_592, B_594, C_593)!=B_594 | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_592, B_594))) | ~v1_funct_2(C_593, A_592, B_594) | ~v1_funct_1(C_593))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.26/5.33  tff(c_8069, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_8063])).
% 12.26/5.33  tff(c_8079, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_8069])).
% 12.26/5.33  tff(c_8080, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_8079])).
% 12.26/5.33  tff(c_8084, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8080, c_590])).
% 12.26/5.33  tff(c_8086, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_8084])).
% 12.26/5.33  tff(c_4492, plain, (k2_relat_1('#skF_4')=k1_relat_1('#skF_3')), inference(splitRight, [status(thm)], [c_3523])).
% 12.26/5.33  tff(c_4493, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4492, c_347])).
% 12.26/5.33  tff(c_8067, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_8063])).
% 12.26/5.33  tff(c_8075, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4493, c_8067])).
% 12.26/5.33  tff(c_8076, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_78, c_8075])).
% 12.26/5.33  tff(c_8138, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8086, c_8076])).
% 12.26/5.33  tff(c_8139, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_8138])).
% 12.26/5.33  tff(c_36, plain, (![A_18]: (v2_funct_1(k6_relat_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_91])).
% 12.26/5.33  tff(c_98, plain, (![A_18]: (v2_funct_1(k6_partfun1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_36])).
% 12.26/5.33  tff(c_8582, plain, (![E_617, B_619, A_616, C_618, D_620]: (k1_xboole_0=C_618 | v2_funct_1(E_617) | k2_relset_1(A_616, B_619, D_620)!=B_619 | ~v2_funct_1(k1_partfun1(A_616, B_619, B_619, C_618, D_620, E_617)) | ~m1_subset_1(E_617, k1_zfmisc_1(k2_zfmisc_1(B_619, C_618))) | ~v1_funct_2(E_617, B_619, C_618) | ~v1_funct_1(E_617) | ~m1_subset_1(D_620, k1_zfmisc_1(k2_zfmisc_1(A_616, B_619))) | ~v1_funct_2(D_620, A_616, B_619) | ~v1_funct_1(D_620))), inference(cnfTransformation, [status(thm)], [f_199])).
% 12.26/5.33  tff(c_8586, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_8582])).
% 12.26/5.33  tff(c_8591, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_98, c_84, c_8586])).
% 12.26/5.33  tff(c_8593, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8139, c_78, c_8591])).
% 12.26/5.33  tff(c_8595, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_8138])).
% 12.26/5.33  tff(c_28, plain, (![A_16]: (k4_relat_1(A_16)=k2_funct_1(A_16) | ~v2_funct_1(A_16) | ~v1_funct_1(A_16) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_79])).
% 12.26/5.33  tff(c_8598, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8595, c_28])).
% 12.26/5.33  tff(c_8601, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_90, c_8598])).
% 12.26/5.33  tff(c_5566, plain, (![A_461, C_462, B_463]: (k6_partfun1(A_461)=k5_relat_1(C_462, k2_funct_1(C_462)) | k1_xboole_0=B_463 | ~v2_funct_1(C_462) | k2_relset_1(A_461, B_463, C_462)!=B_463 | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_461, B_463))) | ~v1_funct_2(C_462, A_461, B_463) | ~v1_funct_1(C_462))), inference(cnfTransformation, [status(thm)], [f_215])).
% 12.26/5.33  tff(c_5572, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_92, c_5566])).
% 12.26/5.33  tff(c_5582, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_84, c_80, c_5572])).
% 12.26/5.33  tff(c_5583, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_76, c_5582])).
% 12.26/5.33  tff(c_5587, plain, (k1_relat_1(k6_partfun1('#skF_1'))=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5583, c_590])).
% 12.26/5.33  tff(c_5589, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_5587])).
% 12.26/5.33  tff(c_5570, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_5566])).
% 12.26/5.33  tff(c_5578, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_88, c_4493, c_5570])).
% 12.26/5.33  tff(c_5579, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4') | k1_relat_1('#skF_3')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_78, c_5578])).
% 12.26/5.33  tff(c_5640, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5589, c_5579])).
% 12.26/5.33  tff(c_5641, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_5640])).
% 12.26/5.33  tff(c_6570, plain, (![C_507, B_508, A_505, D_509, E_506]: (k1_xboole_0=C_507 | v2_funct_1(E_506) | k2_relset_1(A_505, B_508, D_509)!=B_508 | ~v2_funct_1(k1_partfun1(A_505, B_508, B_508, C_507, D_509, E_506)) | ~m1_subset_1(E_506, k1_zfmisc_1(k2_zfmisc_1(B_508, C_507))) | ~v1_funct_2(E_506, B_508, C_507) | ~v1_funct_1(E_506) | ~m1_subset_1(D_509, k1_zfmisc_1(k2_zfmisc_1(A_505, B_508))) | ~v1_funct_2(D_509, A_505, B_508) | ~v1_funct_1(D_509))), inference(cnfTransformation, [status(thm)], [f_199])).
% 12.26/5.33  tff(c_6574, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2110, c_6570])).
% 12.26/5.33  tff(c_6579, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_90, c_88, c_86, c_98, c_84, c_6574])).
% 12.26/5.33  tff(c_6581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5641, c_78, c_6579])).
% 12.26/5.33  tff(c_6583, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_5640])).
% 12.26/5.33  tff(c_6586, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6583, c_28])).
% 12.26/5.33  tff(c_6589, plain, (k4_relat_1('#skF_4')=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_90, c_6586])).
% 12.26/5.33  tff(c_183, plain, (![A_75]: (k9_relat_1(A_75, k1_relat_1(A_75))=k2_relat_1(A_75) | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_48])).
% 12.26/5.33  tff(c_192, plain, (![A_11]: (k9_relat_1(k4_relat_1(A_11), k2_relat_1(A_11))=k2_relat_1(k4_relat_1(A_11)) | ~v1_relat_1(k4_relat_1(A_11)) | ~v1_relat_1(A_11))), inference(superposition, [status(thm), theory('equality')], [c_20, c_183])).
% 12.26/5.33  tff(c_4502, plain, (k9_relat_1(k4_relat_1('#skF_4'), k1_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4492, c_192])).
% 12.26/5.33  tff(c_4513, plain, (k9_relat_1(k4_relat_1('#skF_4'), k1_relat_1('#skF_3'))=k2_relat_1(k4_relat_1('#skF_4')) | ~v1_relat_1(k4_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_4502])).
% 12.26/5.33  tff(c_4526, plain, (~v1_relat_1(k4_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_4513])).
% 12.26/5.33  tff(c_6663, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_6589, c_4526])).
% 12.26/5.33  tff(c_6695, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_32, c_6663])).
% 12.26/5.33  tff(c_6699, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_241, c_90, c_6695])).
% 12.26/5.33  tff(c_6701, plain, (v1_relat_1(k4_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_4513])).
% 12.26/5.33  tff(c_8694, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8601, c_6701])).
% 12.26/5.33  tff(c_12, plain, (![A_8]: (k4_relat_1(k4_relat_1(A_8))=A_8 | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 12.26/5.33  tff(c_8710, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8601, c_12])).
% 12.26/5.33  tff(c_8722, plain, (k4_relat_1(k2_funct_1('#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_8710])).
% 12.26/5.33  tff(c_8594, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_8138])).
% 12.26/5.33  tff(c_8102, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_8086, c_4492])).
% 12.26/5.33  tff(c_8707, plain, (k1_relat_1(k2_funct_1('#skF_4'))=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8601, c_20])).
% 12.26/5.33  tff(c_8720, plain, (k1_relat_1(k2_funct_1('#skF_4'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_241, c_8102, c_8707])).
% 12.26/5.33  tff(c_22, plain, (![A_12, B_14]: (k1_relat_1(k5_relat_1(A_12, B_14))=k1_relat_1(A_12) | ~r1_tarski(k2_relat_1(A_12), k1_relat_1(B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_67])).
% 12.26/5.33  tff(c_8607, plain, (![B_14]: (k1_relat_1(k5_relat_1('#skF_4', B_14))=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', k1_relat_1(B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8102, c_22])).
% 12.26/5.33  tff(c_9699, plain, (![B_663]: (k1_relat_1(k5_relat_1('#skF_4', B_663))=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', k1_relat_1(B_663)) | ~v1_relat_1(B_663))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_8607])).
% 12.26/5.33  tff(c_9729, plain, (k1_relat_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8720, c_9699])).
% 12.26/5.33  tff(c_9769, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8694, c_6, c_101, c_8594, c_9729])).
% 12.26/5.33  tff(c_4499, plain, (![B_14]: (k1_relat_1(k5_relat_1('#skF_4', B_14))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_14)) | ~v1_relat_1(B_14) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4492, c_22])).
% 12.26/5.33  tff(c_4511, plain, (![B_14]: (k1_relat_1(k5_relat_1('#skF_4', B_14))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_4499])).
% 12.26/5.33  tff(c_9484, plain, (![B_660]: (k1_relat_1(k5_relat_1('#skF_4', B_660))=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', k1_relat_1(B_660)) | ~v1_relat_1(B_660))), inference(demodulation, [status(thm), theory('equality')], [c_8086, c_4511])).
% 12.26/5.33  tff(c_9508, plain, (k1_relat_1(k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8720, c_9484])).
% 12.26/5.33  tff(c_9544, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_8694, c_6, c_101, c_8594, c_9508])).
% 12.26/5.33  tff(c_6706, plain, (![B_513]: (k1_relat_1(k5_relat_1('#skF_4', B_513))=k1_relat_1('#skF_4') | ~r1_tarski(k1_relat_1('#skF_3'), k1_relat_1(B_513)) | ~v1_relat_1(B_513))), inference(demodulation, [status(thm), theory('equality')], [c_241, c_4499])).
% 12.26/5.33  tff(c_6755, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_6, c_6706])).
% 12.26/5.33  tff(c_6772, plain, (k1_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_244, c_6755])).
% 12.26/5.33  tff(c_6791, plain, (k9_relat_1(k5_relat_1('#skF_4', '#skF_3'), k1_relat_1('#skF_4'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6772, c_14])).
% 12.26/5.33  tff(c_6861, plain, (~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6791])).
% 12.26/5.33  tff(c_7085, plain, (![F_538, C_539, E_537, D_540, B_536, A_535]: (k1_partfun1(A_535, B_536, C_539, D_540, E_537, F_538)=k5_relat_1(E_537, F_538) | ~m1_subset_1(F_538, k1_zfmisc_1(k2_zfmisc_1(C_539, D_540))) | ~v1_funct_1(F_538) | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(A_535, B_536))) | ~v1_funct_1(E_537))), inference(cnfTransformation, [status(thm)], [f_154])).
% 12.26/5.33  tff(c_7091, plain, (![A_535, B_536, E_537]: (k1_partfun1(A_535, B_536, '#skF_1', '#skF_2', E_537, '#skF_3')=k5_relat_1(E_537, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_537, k1_zfmisc_1(k2_zfmisc_1(A_535, B_536))) | ~v1_funct_1(E_537))), inference(resolution, [status(thm)], [c_92, c_7085])).
% 12.26/5.33  tff(c_7471, plain, (![A_560, B_561, E_562]: (k1_partfun1(A_560, B_561, '#skF_1', '#skF_2', E_562, '#skF_3')=k5_relat_1(E_562, '#skF_3') | ~m1_subset_1(E_562, k1_zfmisc_1(k2_zfmisc_1(A_560, B_561))) | ~v1_funct_1(E_562))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_7091])).
% 12.26/5.33  tff(c_7480, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_86, c_7471])).
% 12.26/5.33  tff(c_7488, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_7480])).
% 12.26/5.33  tff(c_48, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (m1_subset_1(k1_partfun1(A_31, B_32, C_33, D_34, E_35, F_36), k1_zfmisc_1(k2_zfmisc_1(A_31, D_34))) | ~m1_subset_1(F_36, k1_zfmisc_1(k2_zfmisc_1(C_33, D_34))) | ~v1_funct_1(F_36) | ~m1_subset_1(E_35, k1_zfmisc_1(k2_zfmisc_1(A_31, B_32))) | ~v1_funct_1(E_35))), inference(cnfTransformation, [status(thm)], [f_140])).
% 12.26/5.33  tff(c_7756, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_7488, c_48])).
% 12.26/5.33  tff(c_7760, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_86, c_96, c_92, c_7756])).
% 12.26/5.33  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 12.26/5.33  tff(c_7790, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3')) | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_2'))), inference(resolution, [status(thm)], [c_7760, c_8])).
% 12.26/5.33  tff(c_7821, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_7790])).
% 12.26/5.33  tff(c_7823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6861, c_7821])).
% 12.26/5.33  tff(c_7825, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_6791])).
% 12.26/5.33  tff(c_551, plain, (![B_99]: (k1_relat_1(k5_relat_1('#skF_3', B_99))=k1_relat_1('#skF_3') | ~r1_tarski('#skF_2', k1_relat_1(B_99)) | ~v1_relat_1(B_99))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_532])).
% 12.26/5.33  tff(c_9326, plain, (![B_658]: (k1_relat_1(k5_relat_1('#skF_3', B_658))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1(B_658)) | ~v1_relat_1(B_658))), inference(demodulation, [status(thm), theory('equality')], [c_8086, c_551])).
% 12.26/5.33  tff(c_9356, plain, (k1_relat_1(k5_relat_1('#skF_3', k5_relat_1('#skF_4', '#skF_3')))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4')) | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_6772, c_9326])).
% 12.26/5.33  tff(c_9389, plain, (k1_relat_1(k5_relat_1('#skF_3', k5_relat_1('#skF_4', '#skF_3')))='#skF_1' | ~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7825, c_9356])).
% 12.26/5.33  tff(c_9398, plain, (~r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_9389])).
% 12.26/5.33  tff(c_9556, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9544, c_9398])).
% 12.26/5.33  tff(c_9568, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9556])).
% 12.26/5.33  tff(c_9570, plain, (r1_tarski('#skF_2', k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_9389])).
% 12.26/5.33  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.26/5.33  tff(c_9579, plain, (k1_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_9570, c_2])).
% 12.26/5.33  tff(c_9613, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_2')), inference(splitLeft, [status(thm)], [c_9579])).
% 12.26/5.33  tff(c_9781, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9769, c_9613])).
% 12.26/5.33  tff(c_9794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_9781])).
% 12.26/5.33  tff(c_9795, plain, (k1_relat_1('#skF_4')='#skF_2'), inference(splitRight, [status(thm)], [c_9579])).
% 12.26/5.33  tff(c_11354, plain, (![A_706, B_707]: (k2_funct_1(k4_relat_1(A_706))=B_707 | k5_relat_1(B_707, k4_relat_1(A_706))!=k6_partfun1(k1_relat_1(A_706)) | k2_relat_1(B_707)!=k1_relat_1(k4_relat_1(A_706)) | ~v2_funct_1(k4_relat_1(A_706)) | ~v1_funct_1(B_707) | ~v1_relat_1(B_707) | ~v1_funct_1(k4_relat_1(A_706)) | ~v1_relat_1(k4_relat_1(A_706)) | ~v1_relat_1(A_706))), inference(superposition, [status(thm), theory('equality')], [c_18, c_3471])).
% 12.26/5.33  tff(c_11356, plain, (![B_707]: (k2_funct_1(k4_relat_1(k2_funct_1('#skF_4')))=B_707 | k6_partfun1(k1_relat_1(k2_funct_1('#skF_4')))!=k5_relat_1(B_707, '#skF_4') | k2_relat_1(B_707)!=k1_relat_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v2_funct_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v1_funct_1(B_707) | ~v1_relat_1(B_707) | ~v1_funct_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k4_relat_1(k2_funct_1('#skF_4'))) | ~v1_relat_1(k2_funct_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_8722, c_11354])).
% 12.26/5.33  tff(c_19506, plain, (![B_883]: (k2_funct_1('#skF_4')=B_883 | k5_relat_1(B_883, '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1(B_883)!='#skF_2' | ~v1_funct_1(B_883) | ~v1_relat_1(B_883))), inference(demodulation, [status(thm), theory('equality')], [c_8694, c_241, c_8722, c_90, c_8722, c_8595, c_8722, c_9795, c_8722, c_8720, c_8722, c_11356])).
% 12.26/5.33  tff(c_19650, plain, (k2_funct_1('#skF_4')='#skF_3' | k5_relat_1('#skF_3', '#skF_4')!=k6_partfun1('#skF_1') | k2_relat_1('#skF_3')!='#skF_2' | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_244, c_19506])).
% 12.26/5.33  tff(c_19783, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_349, c_9864, c_19650])).
% 12.26/5.33  tff(c_19799, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_19783, c_8594])).
% 12.26/5.33  tff(c_19809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4491, c_19799])).
% 12.26/5.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.26/5.33  
% 12.26/5.33  Inference rules
% 12.26/5.33  ----------------------
% 12.26/5.33  #Ref     : 0
% 12.26/5.33  #Sup     : 4375
% 12.26/5.33  #Fact    : 0
% 12.26/5.33  #Define  : 0
% 12.26/5.33  #Split   : 81
% 12.26/5.33  #Chain   : 0
% 12.26/5.33  #Close   : 0
% 12.26/5.33  
% 12.26/5.33  Ordering : KBO
% 12.26/5.33  
% 12.26/5.33  Simplification rules
% 12.26/5.33  ----------------------
% 12.26/5.33  #Subsume      : 363
% 12.26/5.33  #Demod        : 8177
% 12.26/5.33  #Tautology    : 1660
% 12.26/5.33  #SimpNegUnit  : 257
% 12.26/5.33  #BackRed      : 289
% 12.26/5.33  
% 12.26/5.33  #Partial instantiations: 0
% 12.26/5.33  #Strategies tried      : 1
% 12.26/5.33  
% 12.26/5.33  Timing (in seconds)
% 12.26/5.33  ----------------------
% 12.26/5.34  Preprocessing        : 0.41
% 12.26/5.34  Parsing              : 0.23
% 12.26/5.34  CNF conversion       : 0.03
% 12.26/5.34  Main loop            : 4.09
% 12.26/5.34  Inferencing          : 1.04
% 12.26/5.34  Reduction            : 1.96
% 12.26/5.34  Demodulation         : 1.59
% 12.26/5.34  BG Simplification    : 0.11
% 12.26/5.34  Subsumption          : 0.78
% 12.26/5.34  Abstraction          : 0.14
% 12.26/5.34  MUC search           : 0.00
% 12.26/5.34  Cooper               : 0.00
% 12.26/5.34  Total                : 4.58
% 12.26/5.34  Index Insertion      : 0.00
% 12.26/5.34  Index Deletion       : 0.00
% 12.26/5.34  Index Matching       : 0.00
% 12.26/5.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
