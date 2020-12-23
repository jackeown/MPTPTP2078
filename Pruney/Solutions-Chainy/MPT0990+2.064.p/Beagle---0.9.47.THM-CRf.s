%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:05 EST 2020

% Result     : Theorem 8.55s
% Output     : CNFRefutation 8.79s
% Verified   : 
% Statistics : Number of formulae       :  186 (1633 expanded)
%              Number of leaves         :   54 ( 592 expanded)
%              Depth                    :   21
%              Number of atoms          :  416 (5323 expanded)
%              Number of equality atoms :  141 (1889 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_116,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_80,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_144,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_156,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_62,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_112,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_120,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_42,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_44,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_32,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_128,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_140,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_82,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_funct_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_92,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_154,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_80,plain,(
    k2_funct_1('#skF_4') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_98,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_218,plain,(
    ! [C_83,A_84,B_85] :
      ( v1_relat_1(C_83)
      | ~ m1_subset_1(C_83,k1_zfmisc_1(k2_zfmisc_1(A_84,B_85))) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_239,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_218])).

tff(c_102,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_30,plain,(
    ! [A_19] :
      ( v1_relat_1(k2_funct_1(A_19))
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_86,plain,(
    v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_60,plain,(
    ! [A_40] : m1_subset_1(k6_partfun1(A_40),k1_zfmisc_1(k2_zfmisc_1(A_40,A_40))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_236,plain,(
    ! [A_40] : v1_relat_1(k6_partfun1(A_40)) ),
    inference(resolution,[status(thm)],[c_60,c_218])).

tff(c_64,plain,(
    ! [A_47] : k6_relat_1(A_47) = k6_partfun1(A_47) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_20,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_109,plain,(
    ! [A_15] : k1_relat_1(k6_partfun1(A_15)) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_20])).

tff(c_24,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_265,plain,(
    ! [A_92] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_92)),A_92) = A_92
      | ~ v1_relat_1(A_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_274,plain,(
    ! [A_15] :
      ( k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_15)) = k6_partfun1(A_15)
      | ~ v1_relat_1(k6_partfun1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_265])).

tff(c_278,plain,(
    ! [A_15] : k5_relat_1(k6_partfun1(A_15),k6_partfun1(A_15)) = k6_partfun1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_274])).

tff(c_44,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_relat_1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_103,plain,(
    ! [A_23] :
      ( k5_relat_1(A_23,k2_funct_1(A_23)) = k6_partfun1(k1_relat_1(A_23))
      | ~ v2_funct_1(A_23)
      | ~ v1_funct_1(A_23)
      | ~ v1_relat_1(A_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44])).

tff(c_90,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_406,plain,(
    ! [A_104,B_105,C_106] :
      ( k2_relset_1(A_104,B_105,C_106) = k2_relat_1(C_106)
      | ~ m1_subset_1(C_106,k1_zfmisc_1(k2_zfmisc_1(A_104,B_105))) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_419,plain,(
    k2_relset_1('#skF_2','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_406])).

tff(c_429,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_419])).

tff(c_10,plain,(
    ! [A_4] : k2_subset_1(A_4) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_12,plain,(
    ! [A_5] : m1_subset_1(k2_subset_1(A_5),k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_110,plain,(
    ! [A_5] : m1_subset_1(A_5,k1_zfmisc_1(A_5)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_193,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,B_78)
      | ~ m1_subset_1(A_77,k1_zfmisc_1(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_213,plain,(
    ! [A_5] : r1_tarski(A_5,A_5) ),
    inference(resolution,[status(thm)],[c_110,c_193])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k5_relat_1(B_18,k6_relat_1(A_17)) = B_18
      | ~ r1_tarski(k2_relat_1(B_18),A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_288,plain,(
    ! [B_94,A_95] :
      ( k5_relat_1(B_94,k6_partfun1(A_95)) = B_94
      | ~ r1_tarski(k2_relat_1(B_94),A_95)
      | ~ v1_relat_1(B_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_26])).

tff(c_296,plain,(
    ! [B_94] :
      ( k5_relat_1(B_94,k6_partfun1(k2_relat_1(B_94))) = B_94
      | ~ v1_relat_1(B_94) ) ),
    inference(resolution,[status(thm)],[c_213,c_288])).

tff(c_434,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_296])).

tff(c_441,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_434])).

tff(c_107,plain,(
    ! [A_16] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_16)),A_16) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_24])).

tff(c_601,plain,(
    ! [A_124,B_125,C_126] :
      ( k5_relat_1(k5_relat_1(A_124,B_125),C_126) = k5_relat_1(A_124,k5_relat_1(B_125,C_126))
      | ~ v1_relat_1(C_126)
      | ~ v1_relat_1(B_125)
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_661,plain,(
    ! [A_16,C_126] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_16)),k5_relat_1(A_16,C_126)) = k5_relat_1(A_16,C_126)
      | ~ v1_relat_1(C_126)
      | ~ v1_relat_1(A_16)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_16)))
      | ~ v1_relat_1(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_601])).

tff(c_5748,plain,(
    ! [A_339,C_340] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_339)),k5_relat_1(A_339,C_340)) = k5_relat_1(A_339,C_340)
      | ~ v1_relat_1(C_340)
      | ~ v1_relat_1(A_339) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_661])).

tff(c_5799,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = k5_relat_1('#skF_4',k6_partfun1('#skF_3'))
    | ~ v1_relat_1(k6_partfun1('#skF_3'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_441,c_5748])).

tff(c_5841,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_236,c_441,c_5799])).

tff(c_18,plain,(
    ! [A_8,B_12,C_14] :
      ( k5_relat_1(k5_relat_1(A_8,B_12),C_14) = k5_relat_1(A_8,k5_relat_1(B_12,C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1(B_12)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_5861,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_14)) = k5_relat_1('#skF_4',C_14)
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5841,c_18])).

tff(c_6869,plain,(
    ! [C_379] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k5_relat_1('#skF_4',C_379)) = k5_relat_1('#skF_4',C_379)
      | ~ v1_relat_1(C_379) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_236,c_239,c_5861])).

tff(c_6907,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')),k6_partfun1(k1_relat_1('#skF_4'))) = k5_relat_1('#skF_4',k2_funct_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_6869])).

tff(c_6936,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4'))
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_102,c_86,c_278,c_6907])).

tff(c_6943,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6936])).

tff(c_6946,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_6943])).

tff(c_6950,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_102,c_6946])).

tff(c_6952,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6936])).

tff(c_92,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_238,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_218])).

tff(c_6,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_121,plain,(
    ! [A_65] :
      ( k1_xboole_0 = A_65
      | ~ v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_129,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_121])).

tff(c_84,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_138,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_84])).

tff(c_96,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_94,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_427,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_406])).

tff(c_78,plain,(
    ! [A_59,C_61,B_60] :
      ( k6_partfun1(A_59) = k5_relat_1(C_61,k2_funct_1(C_61))
      | k1_xboole_0 = B_60
      | ~ v2_funct_1(C_61)
      | k2_relset_1(A_59,B_60,C_61) != B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_7284,plain,(
    ! [A_399,C_400,B_401] :
      ( k6_partfun1(A_399) = k5_relat_1(C_400,k2_funct_1(C_400))
      | B_401 = '#skF_1'
      | ~ v2_funct_1(C_400)
      | k2_relset_1(A_399,B_401,C_400) != B_401
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(A_399,B_401)))
      | ~ v1_funct_2(C_400,A_399,B_401)
      | ~ v1_funct_1(C_400) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_78])).

tff(c_7291,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_7284])).

tff(c_7303,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_427,c_7291])).

tff(c_7304,plain,
    ( k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3')
    | ~ v2_funct_1('#skF_5')
    | k2_relat_1('#skF_5') != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_7303])).

tff(c_7416,plain,(
    k2_relat_1('#skF_5') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7304])).

tff(c_100,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_388,plain,(
    ! [A_101,B_102,D_103] :
      ( r2_relset_1(A_101,B_102,D_103,D_103)
      | ~ m1_subset_1(D_103,k1_zfmisc_1(k2_zfmisc_1(A_101,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_401,plain,(
    ! [A_40] : r2_relset_1(A_40,A_40,k6_partfun1(A_40),k6_partfun1(A_40)) ),
    inference(resolution,[status(thm)],[c_60,c_388])).

tff(c_6754,plain,(
    ! [A_372,E_375,D_373,F_374,C_377,B_376] :
      ( m1_subset_1(k1_partfun1(A_372,B_376,C_377,D_373,E_375,F_374),k1_zfmisc_1(k2_zfmisc_1(A_372,D_373)))
      | ~ m1_subset_1(F_374,k1_zfmisc_1(k2_zfmisc_1(C_377,D_373)))
      | ~ v1_funct_1(F_374)
      | ~ m1_subset_1(E_375,k1_zfmisc_1(k2_zfmisc_1(A_372,B_376)))
      | ~ v1_funct_1(E_375) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_88,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_5718,plain,(
    ! [D_335,C_336,A_337,B_338] :
      ( D_335 = C_336
      | ~ r2_relset_1(A_337,B_338,C_336,D_335)
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338)))
      | ~ m1_subset_1(C_336,k1_zfmisc_1(k2_zfmisc_1(A_337,B_338))) ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5728,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_88,c_5718])).

tff(c_5747,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_5728])).

tff(c_5884,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_5747])).

tff(c_6774,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6754,c_5884])).

tff(c_6796,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_98,c_96,c_92,c_6774])).

tff(c_6797,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_5747])).

tff(c_7984,plain,(
    ! [A_430,B_431,C_432,D_433] :
      ( k2_relset_1(A_430,B_431,C_432) = B_431
      | ~ r2_relset_1(B_431,B_431,k1_partfun1(B_431,A_430,A_430,B_431,D_433,C_432),k6_partfun1(B_431))
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(B_431,A_430)))
      | ~ v1_funct_2(D_433,B_431,A_430)
      | ~ v1_funct_1(D_433)
      | ~ m1_subset_1(C_432,k1_zfmisc_1(k2_zfmisc_1(A_430,B_431)))
      | ~ v1_funct_2(C_432,A_430,B_431)
      | ~ v1_funct_1(C_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_7990,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_6797,c_7984])).

tff(c_7994,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_92,c_102,c_100,c_98,c_401,c_427,c_7990])).

tff(c_7996,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_7416,c_7994])).

tff(c_7998,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_7304])).

tff(c_8003,plain,
    ( k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7998,c_296])).

tff(c_8010,plain,(
    k5_relat_1('#skF_5',k6_partfun1('#skF_2')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_8003])).

tff(c_82,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_137,plain,(
    '#skF_3' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_82])).

tff(c_6951,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1(k1_relat_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6936])).

tff(c_7293,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_7284])).

tff(c_7307,plain,
    ( k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2')
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_90,c_86,c_6951,c_7293])).

tff(c_7308,plain,(
    k6_partfun1(k1_relat_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_137,c_7307])).

tff(c_7313,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7308,c_6951])).

tff(c_7999,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7998,c_427])).

tff(c_76,plain,(
    ! [B_60,C_61,A_59] :
      ( k6_partfun1(B_60) = k5_relat_1(k2_funct_1(C_61),C_61)
      | k1_xboole_0 = B_60
      | ~ v2_funct_1(C_61)
      | k2_relset_1(A_59,B_60,C_61) != B_60
      | ~ m1_subset_1(C_61,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ v1_funct_2(C_61,A_59,B_60)
      | ~ v1_funct_1(C_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_8083,plain,(
    ! [B_437,C_438,A_439] :
      ( k6_partfun1(B_437) = k5_relat_1(k2_funct_1(C_438),C_438)
      | B_437 = '#skF_1'
      | ~ v2_funct_1(C_438)
      | k2_relset_1(A_439,B_437,C_438) != B_437
      | ~ m1_subset_1(C_438,k1_zfmisc_1(k2_zfmisc_1(A_439,B_437)))
      | ~ v1_funct_2(C_438,A_439,B_437)
      | ~ v1_funct_1(C_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_76])).

tff(c_8090,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5')
    | k2_relset_1('#skF_3','#skF_2','#skF_5') != '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_92,c_8083])).

tff(c_8102,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | '#skF_2' = '#skF_1'
    | ~ v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_94,c_7999,c_8090])).

tff(c_8103,plain,
    ( k5_relat_1(k2_funct_1('#skF_5'),'#skF_5') = k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_138,c_8102])).

tff(c_8178,plain,(
    ~ v2_funct_1('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_8103])).

tff(c_32,plain,(
    ! [A_20] : v2_funct_1(k6_relat_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_105,plain,(
    ! [A_20] : v2_funct_1(k6_partfun1(A_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_32])).

tff(c_70,plain,(
    ! [A_53,D_56,E_58,C_55,B_54] :
      ( k1_xboole_0 = C_55
      | v2_funct_1(E_58)
      | k2_relset_1(A_53,B_54,D_56) != B_54
      | ~ v2_funct_1(k1_partfun1(A_53,B_54,B_54,C_55,D_56,E_58))
      | ~ m1_subset_1(E_58,k1_zfmisc_1(k2_zfmisc_1(B_54,C_55)))
      | ~ v1_funct_2(E_58,B_54,C_55)
      | ~ v1_funct_1(E_58)
      | ~ m1_subset_1(D_56,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54)))
      | ~ v1_funct_2(D_56,A_53,B_54)
      | ~ v1_funct_1(D_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_199])).

tff(c_8711,plain,(
    ! [D_470,B_471,C_468,E_467,A_469] :
      ( C_468 = '#skF_1'
      | v2_funct_1(E_467)
      | k2_relset_1(A_469,B_471,D_470) != B_471
      | ~ v2_funct_1(k1_partfun1(A_469,B_471,B_471,C_468,D_470,E_467))
      | ~ m1_subset_1(E_467,k1_zfmisc_1(k2_zfmisc_1(B_471,C_468)))
      | ~ v1_funct_2(E_467,B_471,C_468)
      | ~ v1_funct_1(E_467)
      | ~ m1_subset_1(D_470,k1_zfmisc_1(k2_zfmisc_1(A_469,B_471)))
      | ~ v1_funct_2(D_470,A_469,B_471)
      | ~ v1_funct_1(D_470) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_70])).

tff(c_8715,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5')
    | k2_relset_1('#skF_2','#skF_3','#skF_4') != '#skF_3'
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6797,c_8711])).

tff(c_8720,plain,
    ( '#skF_2' = '#skF_1'
    | v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_100,c_98,c_96,c_94,c_92,c_105,c_90,c_8715])).

tff(c_8722,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8178,c_138,c_8720])).

tff(c_8724,plain,(
    v2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_8103])).

tff(c_313,plain,(
    ! [A_97] :
      ( k1_relat_1(k2_funct_1(A_97)) = k2_relat_1(A_97)
      | ~ v2_funct_1(A_97)
      | ~ v1_funct_1(A_97)
      | ~ v1_relat_1(A_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9497,plain,(
    ! [A_505] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_505)),k2_funct_1(A_505)) = k2_funct_1(A_505)
      | ~ v1_relat_1(k2_funct_1(A_505))
      | ~ v2_funct_1(A_505)
      | ~ v1_funct_1(A_505)
      | ~ v1_relat_1(A_505) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_313,c_107])).

tff(c_9515,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5'))
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7998,c_9497])).

tff(c_9536,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_96,c_8724,c_9515])).

tff(c_9566,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9536])).

tff(c_9570,plain,
    ( ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_9566])).

tff(c_9574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_96,c_9570])).

tff(c_9576,plain,(
    v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9536])).

tff(c_7997,plain,
    ( ~ v2_funct_1('#skF_5')
    | k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_7304])).

tff(c_8789,plain,(
    k5_relat_1('#skF_5',k2_funct_1('#skF_5')) = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8724,c_7997])).

tff(c_9575,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_5')) = k2_funct_1('#skF_5') ),
    inference(splitRight,[status(thm)],[c_9536])).

tff(c_7213,plain,(
    ! [A_391,B_395,D_393,E_390,C_392,F_394] :
      ( k1_partfun1(A_391,B_395,C_392,D_393,E_390,F_394) = k5_relat_1(E_390,F_394)
      | ~ m1_subset_1(F_394,k1_zfmisc_1(k2_zfmisc_1(C_392,D_393)))
      | ~ v1_funct_1(F_394)
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_395)))
      | ~ v1_funct_1(E_390) ) ),
    inference(cnfTransformation,[status(thm)],[f_154])).

tff(c_7220,plain,(
    ! [A_391,B_395,E_390] :
      ( k1_partfun1(A_391,B_395,'#skF_3','#skF_2',E_390,'#skF_5') = k5_relat_1(E_390,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_390,k1_zfmisc_1(k2_zfmisc_1(A_391,B_395)))
      | ~ v1_funct_1(E_390) ) ),
    inference(resolution,[status(thm)],[c_92,c_7213])).

tff(c_9103,plain,(
    ! [A_483,B_484,E_485] :
      ( k1_partfun1(A_483,B_484,'#skF_3','#skF_2',E_485,'#skF_5') = k5_relat_1(E_485,'#skF_5')
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(A_483,B_484)))
      | ~ v1_funct_1(E_485) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_7220])).

tff(c_9125,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_98,c_9103])).

tff(c_9144,plain,(
    k5_relat_1('#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_6797,c_9125])).

tff(c_9152,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_14) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9144,c_18])).

tff(c_9158,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_14) = k5_relat_1('#skF_4',k5_relat_1('#skF_5',C_14))
      | ~ v1_relat_1(C_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_238,c_9152])).

tff(c_9580,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_5',k2_funct_1('#skF_5'))) = k2_funct_1('#skF_5')
    | ~ v1_relat_1(k2_funct_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9575,c_9158])).

tff(c_9596,plain,(
    k2_funct_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9576,c_441,c_8789,c_9580])).

tff(c_9608,plain,(
    k5_relat_1('#skF_5','#skF_4') = k6_partfun1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9596,c_8789])).

tff(c_9744,plain,(
    ! [C_14] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_14) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_14))
      | ~ v1_relat_1(C_14)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9608,c_18])).

tff(c_10030,plain,(
    ! [C_521] :
      ( k5_relat_1(k6_partfun1('#skF_3'),C_521) = k5_relat_1('#skF_5',k5_relat_1('#skF_4',C_521))
      | ~ v1_relat_1(C_521) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_238,c_239,c_9744])).

tff(c_9521,plain,
    ( k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_9497])).

tff(c_9538,plain,(
    k5_relat_1(k6_partfun1('#skF_3'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_102,c_86,c_6952,c_9521])).

tff(c_10039,plain,
    ( k5_relat_1('#skF_5',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_10030,c_9538])).

tff(c_10117,plain,(
    k2_funct_1('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6952,c_8010,c_7313,c_10039])).

tff(c_10119,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_10117])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:26:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.55/2.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/2.92  
% 8.55/2.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.55/2.92  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_subset_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.55/2.92  
% 8.55/2.92  %Foreground sorts:
% 8.55/2.92  
% 8.55/2.92  
% 8.55/2.92  %Background operators:
% 8.55/2.92  
% 8.55/2.92  
% 8.55/2.92  %Foreground operators:
% 8.55/2.92  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.55/2.92  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 8.55/2.92  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.55/2.92  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.55/2.92  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.55/2.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.55/2.92  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.55/2.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.55/2.92  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.55/2.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.55/2.92  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.55/2.92  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.55/2.92  tff('#skF_5', type, '#skF_5': $i).
% 8.55/2.92  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.55/2.92  tff('#skF_2', type, '#skF_2': $i).
% 8.55/2.92  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.55/2.92  tff('#skF_3', type, '#skF_3': $i).
% 8.55/2.92  tff('#skF_1', type, '#skF_1': $i).
% 8.55/2.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.55/2.92  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.55/2.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.55/2.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.55/2.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.55/2.92  tff('#skF_4', type, '#skF_4': $i).
% 8.55/2.92  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.55/2.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.55/2.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 8.55/2.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.55/2.92  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.55/2.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.55/2.92  
% 8.79/2.95  tff(f_241, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 8.79/2.95  tff(f_116, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.79/2.95  tff(f_80, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.79/2.95  tff(f_144, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.79/2.95  tff(f_156, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.79/2.95  tff(f_62, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 8.79/2.95  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_relat_1)).
% 8.79/2.95  tff(f_112, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 8.79/2.95  tff(f_120, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.79/2.95  tff(f_42, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 8.79/2.95  tff(f_44, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 8.79/2.95  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 8.79/2.95  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 8.79/2.95  tff(f_58, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 8.79/2.95  tff(f_32, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 8.79/2.95  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 8.79/2.95  tff(f_215, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 8.79/2.95  tff(f_128, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.79/2.95  tff(f_140, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.79/2.95  tff(f_173, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_funct_2)).
% 8.79/2.95  tff(f_82, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t52_funct_1)).
% 8.79/2.95  tff(f_199, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_funct_2)).
% 8.79/2.95  tff(f_92, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_funct_1)).
% 8.79/2.95  tff(f_154, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.79/2.95  tff(c_80, plain, (k2_funct_1('#skF_4')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_98, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_218, plain, (![C_83, A_84, B_85]: (v1_relat_1(C_83) | ~m1_subset_1(C_83, k1_zfmisc_1(k2_zfmisc_1(A_84, B_85))))), inference(cnfTransformation, [status(thm)], [f_116])).
% 8.79/2.95  tff(c_239, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_218])).
% 8.79/2.95  tff(c_102, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_30, plain, (![A_19]: (v1_relat_1(k2_funct_1(A_19)) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.79/2.95  tff(c_86, plain, (v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_60, plain, (![A_40]: (m1_subset_1(k6_partfun1(A_40), k1_zfmisc_1(k2_zfmisc_1(A_40, A_40))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 8.79/2.95  tff(c_236, plain, (![A_40]: (v1_relat_1(k6_partfun1(A_40)))), inference(resolution, [status(thm)], [c_60, c_218])).
% 8.79/2.95  tff(c_64, plain, (![A_47]: (k6_relat_1(A_47)=k6_partfun1(A_47))), inference(cnfTransformation, [status(thm)], [f_156])).
% 8.79/2.95  tff(c_20, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.79/2.95  tff(c_109, plain, (![A_15]: (k1_relat_1(k6_partfun1(A_15))=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_64, c_20])).
% 8.79/2.95  tff(c_24, plain, (![A_16]: (k5_relat_1(k6_relat_1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 8.79/2.95  tff(c_265, plain, (![A_92]: (k5_relat_1(k6_partfun1(k1_relat_1(A_92)), A_92)=A_92 | ~v1_relat_1(A_92))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 8.79/2.95  tff(c_274, plain, (![A_15]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_15))=k6_partfun1(A_15) | ~v1_relat_1(k6_partfun1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_109, c_265])).
% 8.79/2.95  tff(c_278, plain, (![A_15]: (k5_relat_1(k6_partfun1(A_15), k6_partfun1(A_15))=k6_partfun1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_274])).
% 8.79/2.95  tff(c_44, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_relat_1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_112])).
% 8.79/2.95  tff(c_103, plain, (![A_23]: (k5_relat_1(A_23, k2_funct_1(A_23))=k6_partfun1(k1_relat_1(A_23)) | ~v2_funct_1(A_23) | ~v1_funct_1(A_23) | ~v1_relat_1(A_23))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44])).
% 8.79/2.95  tff(c_90, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')='#skF_3'), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_406, plain, (![A_104, B_105, C_106]: (k2_relset_1(A_104, B_105, C_106)=k2_relat_1(C_106) | ~m1_subset_1(C_106, k1_zfmisc_1(k2_zfmisc_1(A_104, B_105))))), inference(cnfTransformation, [status(thm)], [f_120])).
% 8.79/2.95  tff(c_419, plain, (k2_relset_1('#skF_2', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_406])).
% 8.79/2.95  tff(c_429, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_419])).
% 8.79/2.95  tff(c_10, plain, (![A_4]: (k2_subset_1(A_4)=A_4)), inference(cnfTransformation, [status(thm)], [f_42])).
% 8.79/2.95  tff(c_12, plain, (![A_5]: (m1_subset_1(k2_subset_1(A_5), k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 8.79/2.95  tff(c_110, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 8.79/2.95  tff(c_193, plain, (![A_77, B_78]: (r1_tarski(A_77, B_78) | ~m1_subset_1(A_77, k1_zfmisc_1(B_78)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 8.79/2.95  tff(c_213, plain, (![A_5]: (r1_tarski(A_5, A_5))), inference(resolution, [status(thm)], [c_110, c_193])).
% 8.79/2.95  tff(c_26, plain, (![B_18, A_17]: (k5_relat_1(B_18, k6_relat_1(A_17))=B_18 | ~r1_tarski(k2_relat_1(B_18), A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.79/2.95  tff(c_288, plain, (![B_94, A_95]: (k5_relat_1(B_94, k6_partfun1(A_95))=B_94 | ~r1_tarski(k2_relat_1(B_94), A_95) | ~v1_relat_1(B_94))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_26])).
% 8.79/2.95  tff(c_296, plain, (![B_94]: (k5_relat_1(B_94, k6_partfun1(k2_relat_1(B_94)))=B_94 | ~v1_relat_1(B_94))), inference(resolution, [status(thm)], [c_213, c_288])).
% 8.79/2.95  tff(c_434, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_429, c_296])).
% 8.79/2.95  tff(c_441, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_434])).
% 8.79/2.95  tff(c_107, plain, (![A_16]: (k5_relat_1(k6_partfun1(k1_relat_1(A_16)), A_16)=A_16 | ~v1_relat_1(A_16))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_24])).
% 8.79/2.95  tff(c_601, plain, (![A_124, B_125, C_126]: (k5_relat_1(k5_relat_1(A_124, B_125), C_126)=k5_relat_1(A_124, k5_relat_1(B_125, C_126)) | ~v1_relat_1(C_126) | ~v1_relat_1(B_125) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.79/2.95  tff(c_661, plain, (![A_16, C_126]: (k5_relat_1(k6_partfun1(k1_relat_1(A_16)), k5_relat_1(A_16, C_126))=k5_relat_1(A_16, C_126) | ~v1_relat_1(C_126) | ~v1_relat_1(A_16) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_16))) | ~v1_relat_1(A_16))), inference(superposition, [status(thm), theory('equality')], [c_107, c_601])).
% 8.79/2.95  tff(c_5748, plain, (![A_339, C_340]: (k5_relat_1(k6_partfun1(k1_relat_1(A_339)), k5_relat_1(A_339, C_340))=k5_relat_1(A_339, C_340) | ~v1_relat_1(C_340) | ~v1_relat_1(A_339))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_661])).
% 8.79/2.95  tff(c_5799, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')=k5_relat_1('#skF_4', k6_partfun1('#skF_3')) | ~v1_relat_1(k6_partfun1('#skF_3')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_441, c_5748])).
% 8.79/2.95  tff(c_5841, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_236, c_441, c_5799])).
% 8.79/2.95  tff(c_18, plain, (![A_8, B_12, C_14]: (k5_relat_1(k5_relat_1(A_8, B_12), C_14)=k5_relat_1(A_8, k5_relat_1(B_12, C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1(B_12) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_58])).
% 8.79/2.95  tff(c_5861, plain, (![C_14]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_14))=k5_relat_1('#skF_4', C_14) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_4') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_4'))))), inference(superposition, [status(thm), theory('equality')], [c_5841, c_18])).
% 8.79/2.95  tff(c_6869, plain, (![C_379]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k5_relat_1('#skF_4', C_379))=k5_relat_1('#skF_4', C_379) | ~v1_relat_1(C_379))), inference(demodulation, [status(thm), theory('equality')], [c_236, c_239, c_5861])).
% 8.79/2.95  tff(c_6907, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_4')), k6_partfun1(k1_relat_1('#skF_4')))=k5_relat_1('#skF_4', k2_funct_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_103, c_6869])).
% 8.79/2.95  tff(c_6936, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4')) | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_102, c_86, c_278, c_6907])).
% 8.79/2.95  tff(c_6943, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6936])).
% 8.79/2.95  tff(c_6946, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_6943])).
% 8.79/2.95  tff(c_6950, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_102, c_6946])).
% 8.79/2.95  tff(c_6952, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6936])).
% 8.79/2.95  tff(c_92, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_238, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_218])).
% 8.79/2.95  tff(c_6, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.79/2.95  tff(c_121, plain, (![A_65]: (k1_xboole_0=A_65 | ~v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_30])).
% 8.79/2.95  tff(c_129, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_6, c_121])).
% 8.79/2.95  tff(c_84, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_138, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_84])).
% 8.79/2.95  tff(c_96, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_94, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_427, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_406])).
% 8.79/2.95  tff(c_78, plain, (![A_59, C_61, B_60]: (k6_partfun1(A_59)=k5_relat_1(C_61, k2_funct_1(C_61)) | k1_xboole_0=B_60 | ~v2_funct_1(C_61) | k2_relset_1(A_59, B_60, C_61)!=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_215])).
% 8.79/2.95  tff(c_7284, plain, (![A_399, C_400, B_401]: (k6_partfun1(A_399)=k5_relat_1(C_400, k2_funct_1(C_400)) | B_401='#skF_1' | ~v2_funct_1(C_400) | k2_relset_1(A_399, B_401, C_400)!=B_401 | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(A_399, B_401))) | ~v1_funct_2(C_400, A_399, B_401) | ~v1_funct_1(C_400))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_78])).
% 8.79/2.95  tff(c_7291, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_7284])).
% 8.79/2.95  tff(c_7303, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_427, c_7291])).
% 8.79/2.95  tff(c_7304, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3') | ~v2_funct_1('#skF_5') | k2_relat_1('#skF_5')!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_138, c_7303])).
% 8.79/2.95  tff(c_7416, plain, (k2_relat_1('#skF_5')!='#skF_2'), inference(splitLeft, [status(thm)], [c_7304])).
% 8.79/2.95  tff(c_100, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_388, plain, (![A_101, B_102, D_103]: (r2_relset_1(A_101, B_102, D_103, D_103) | ~m1_subset_1(D_103, k1_zfmisc_1(k2_zfmisc_1(A_101, B_102))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.79/2.95  tff(c_401, plain, (![A_40]: (r2_relset_1(A_40, A_40, k6_partfun1(A_40), k6_partfun1(A_40)))), inference(resolution, [status(thm)], [c_60, c_388])).
% 8.79/2.95  tff(c_6754, plain, (![A_372, E_375, D_373, F_374, C_377, B_376]: (m1_subset_1(k1_partfun1(A_372, B_376, C_377, D_373, E_375, F_374), k1_zfmisc_1(k2_zfmisc_1(A_372, D_373))) | ~m1_subset_1(F_374, k1_zfmisc_1(k2_zfmisc_1(C_377, D_373))) | ~v1_funct_1(F_374) | ~m1_subset_1(E_375, k1_zfmisc_1(k2_zfmisc_1(A_372, B_376))) | ~v1_funct_1(E_375))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.79/2.95  tff(c_88, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_5718, plain, (![D_335, C_336, A_337, B_338]: (D_335=C_336 | ~r2_relset_1(A_337, B_338, C_336, D_335) | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))) | ~m1_subset_1(C_336, k1_zfmisc_1(k2_zfmisc_1(A_337, B_338))))), inference(cnfTransformation, [status(thm)], [f_128])).
% 8.79/2.95  tff(c_5728, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_88, c_5718])).
% 8.79/2.95  tff(c_5747, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_5728])).
% 8.79/2.95  tff(c_5884, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_5747])).
% 8.79/2.95  tff(c_6774, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_6754, c_5884])).
% 8.79/2.95  tff(c_6796, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_102, c_98, c_96, c_92, c_6774])).
% 8.79/2.95  tff(c_6797, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_5747])).
% 8.79/2.95  tff(c_7984, plain, (![A_430, B_431, C_432, D_433]: (k2_relset_1(A_430, B_431, C_432)=B_431 | ~r2_relset_1(B_431, B_431, k1_partfun1(B_431, A_430, A_430, B_431, D_433, C_432), k6_partfun1(B_431)) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(B_431, A_430))) | ~v1_funct_2(D_433, B_431, A_430) | ~v1_funct_1(D_433) | ~m1_subset_1(C_432, k1_zfmisc_1(k2_zfmisc_1(A_430, B_431))) | ~v1_funct_2(C_432, A_430, B_431) | ~v1_funct_1(C_432))), inference(cnfTransformation, [status(thm)], [f_173])).
% 8.79/2.95  tff(c_7990, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_6797, c_7984])).
% 8.79/2.95  tff(c_7994, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_92, c_102, c_100, c_98, c_401, c_427, c_7990])).
% 8.79/2.95  tff(c_7996, plain, $false, inference(negUnitSimplification, [status(thm)], [c_7416, c_7994])).
% 8.79/2.95  tff(c_7998, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(splitRight, [status(thm)], [c_7304])).
% 8.79/2.95  tff(c_8003, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5' | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7998, c_296])).
% 8.79/2.95  tff(c_8010, plain, (k5_relat_1('#skF_5', k6_partfun1('#skF_2'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_238, c_8003])).
% 8.79/2.95  tff(c_82, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_241])).
% 8.79/2.95  tff(c_137, plain, ('#skF_3'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_129, c_82])).
% 8.79/2.95  tff(c_6951, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1(k1_relat_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6936])).
% 8.79/2.95  tff(c_7293, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_7284])).
% 8.79/2.95  tff(c_7307, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2') | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_90, c_86, c_6951, c_7293])).
% 8.79/2.95  tff(c_7308, plain, (k6_partfun1(k1_relat_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_137, c_7307])).
% 8.79/2.95  tff(c_7313, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_7308, c_6951])).
% 8.79/2.95  tff(c_7999, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7998, c_427])).
% 8.79/2.95  tff(c_76, plain, (![B_60, C_61, A_59]: (k6_partfun1(B_60)=k5_relat_1(k2_funct_1(C_61), C_61) | k1_xboole_0=B_60 | ~v2_funct_1(C_61) | k2_relset_1(A_59, B_60, C_61)!=B_60 | ~m1_subset_1(C_61, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~v1_funct_2(C_61, A_59, B_60) | ~v1_funct_1(C_61))), inference(cnfTransformation, [status(thm)], [f_215])).
% 8.79/2.95  tff(c_8083, plain, (![B_437, C_438, A_439]: (k6_partfun1(B_437)=k5_relat_1(k2_funct_1(C_438), C_438) | B_437='#skF_1' | ~v2_funct_1(C_438) | k2_relset_1(A_439, B_437, C_438)!=B_437 | ~m1_subset_1(C_438, k1_zfmisc_1(k2_zfmisc_1(A_439, B_437))) | ~v1_funct_2(C_438, A_439, B_437) | ~v1_funct_1(C_438))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_76])).
% 8.79/2.95  tff(c_8090, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5') | k2_relset_1('#skF_3', '#skF_2', '#skF_5')!='#skF_2' | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_92, c_8083])).
% 8.79/2.95  tff(c_8102, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | '#skF_2'='#skF_1' | ~v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_96, c_94, c_7999, c_8090])).
% 8.79/2.95  tff(c_8103, plain, (k5_relat_1(k2_funct_1('#skF_5'), '#skF_5')=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_138, c_8102])).
% 8.79/2.95  tff(c_8178, plain, (~v2_funct_1('#skF_5')), inference(splitLeft, [status(thm)], [c_8103])).
% 8.79/2.95  tff(c_32, plain, (![A_20]: (v2_funct_1(k6_relat_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 8.79/2.95  tff(c_105, plain, (![A_20]: (v2_funct_1(k6_partfun1(A_20)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_32])).
% 8.79/2.95  tff(c_70, plain, (![A_53, D_56, E_58, C_55, B_54]: (k1_xboole_0=C_55 | v2_funct_1(E_58) | k2_relset_1(A_53, B_54, D_56)!=B_54 | ~v2_funct_1(k1_partfun1(A_53, B_54, B_54, C_55, D_56, E_58)) | ~m1_subset_1(E_58, k1_zfmisc_1(k2_zfmisc_1(B_54, C_55))) | ~v1_funct_2(E_58, B_54, C_55) | ~v1_funct_1(E_58) | ~m1_subset_1(D_56, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))) | ~v1_funct_2(D_56, A_53, B_54) | ~v1_funct_1(D_56))), inference(cnfTransformation, [status(thm)], [f_199])).
% 8.79/2.95  tff(c_8711, plain, (![D_470, B_471, C_468, E_467, A_469]: (C_468='#skF_1' | v2_funct_1(E_467) | k2_relset_1(A_469, B_471, D_470)!=B_471 | ~v2_funct_1(k1_partfun1(A_469, B_471, B_471, C_468, D_470, E_467)) | ~m1_subset_1(E_467, k1_zfmisc_1(k2_zfmisc_1(B_471, C_468))) | ~v1_funct_2(E_467, B_471, C_468) | ~v1_funct_1(E_467) | ~m1_subset_1(D_470, k1_zfmisc_1(k2_zfmisc_1(A_469, B_471))) | ~v1_funct_2(D_470, A_469, B_471) | ~v1_funct_1(D_470))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_70])).
% 8.79/2.95  tff(c_8715, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5') | k2_relset_1('#skF_2', '#skF_3', '#skF_4')!='#skF_3' | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6797, c_8711])).
% 8.79/2.95  tff(c_8720, plain, ('#skF_2'='#skF_1' | v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_100, c_98, c_96, c_94, c_92, c_105, c_90, c_8715])).
% 8.79/2.95  tff(c_8722, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8178, c_138, c_8720])).
% 8.79/2.95  tff(c_8724, plain, (v2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_8103])).
% 8.79/2.95  tff(c_313, plain, (![A_97]: (k1_relat_1(k2_funct_1(A_97))=k2_relat_1(A_97) | ~v2_funct_1(A_97) | ~v1_funct_1(A_97) | ~v1_relat_1(A_97))), inference(cnfTransformation, [status(thm)], [f_92])).
% 8.79/2.95  tff(c_9497, plain, (![A_505]: (k5_relat_1(k6_partfun1(k2_relat_1(A_505)), k2_funct_1(A_505))=k2_funct_1(A_505) | ~v1_relat_1(k2_funct_1(A_505)) | ~v2_funct_1(A_505) | ~v1_funct_1(A_505) | ~v1_relat_1(A_505))), inference(superposition, [status(thm), theory('equality')], [c_313, c_107])).
% 8.79/2.95  tff(c_9515, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5')) | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7998, c_9497])).
% 8.79/2.95  tff(c_9536, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_96, c_8724, c_9515])).
% 8.79/2.95  tff(c_9566, plain, (~v1_relat_1(k2_funct_1('#skF_5'))), inference(splitLeft, [status(thm)], [c_9536])).
% 8.79/2.95  tff(c_9570, plain, (~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_30, c_9566])).
% 8.79/2.95  tff(c_9574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_238, c_96, c_9570])).
% 8.79/2.95  tff(c_9576, plain, (v1_relat_1(k2_funct_1('#skF_5'))), inference(splitRight, [status(thm)], [c_9536])).
% 8.79/2.95  tff(c_7997, plain, (~v2_funct_1('#skF_5') | k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(splitRight, [status(thm)], [c_7304])).
% 8.79/2.95  tff(c_8789, plain, (k5_relat_1('#skF_5', k2_funct_1('#skF_5'))=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_8724, c_7997])).
% 8.79/2.95  tff(c_9575, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_5'))=k2_funct_1('#skF_5')), inference(splitRight, [status(thm)], [c_9536])).
% 8.79/2.95  tff(c_7213, plain, (![A_391, B_395, D_393, E_390, C_392, F_394]: (k1_partfun1(A_391, B_395, C_392, D_393, E_390, F_394)=k5_relat_1(E_390, F_394) | ~m1_subset_1(F_394, k1_zfmisc_1(k2_zfmisc_1(C_392, D_393))) | ~v1_funct_1(F_394) | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_395))) | ~v1_funct_1(E_390))), inference(cnfTransformation, [status(thm)], [f_154])).
% 8.79/2.95  tff(c_7220, plain, (![A_391, B_395, E_390]: (k1_partfun1(A_391, B_395, '#skF_3', '#skF_2', E_390, '#skF_5')=k5_relat_1(E_390, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_390, k1_zfmisc_1(k2_zfmisc_1(A_391, B_395))) | ~v1_funct_1(E_390))), inference(resolution, [status(thm)], [c_92, c_7213])).
% 8.79/2.95  tff(c_9103, plain, (![A_483, B_484, E_485]: (k1_partfun1(A_483, B_484, '#skF_3', '#skF_2', E_485, '#skF_5')=k5_relat_1(E_485, '#skF_5') | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(A_483, B_484))) | ~v1_funct_1(E_485))), inference(demodulation, [status(thm), theory('equality')], [c_96, c_7220])).
% 8.79/2.95  tff(c_9125, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_98, c_9103])).
% 8.79/2.95  tff(c_9144, plain, (k5_relat_1('#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_6797, c_9125])).
% 8.79/2.95  tff(c_9152, plain, (![C_14]: (k5_relat_1(k6_partfun1('#skF_2'), C_14)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_5') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_9144, c_18])).
% 8.79/2.95  tff(c_9158, plain, (![C_14]: (k5_relat_1(k6_partfun1('#skF_2'), C_14)=k5_relat_1('#skF_4', k5_relat_1('#skF_5', C_14)) | ~v1_relat_1(C_14))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_238, c_9152])).
% 8.79/2.95  tff(c_9580, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_5', k2_funct_1('#skF_5')))=k2_funct_1('#skF_5') | ~v1_relat_1(k2_funct_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9575, c_9158])).
% 8.79/2.95  tff(c_9596, plain, (k2_funct_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_9576, c_441, c_8789, c_9580])).
% 8.79/2.95  tff(c_9608, plain, (k5_relat_1('#skF_5', '#skF_4')=k6_partfun1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9596, c_8789])).
% 8.79/2.95  tff(c_9744, plain, (![C_14]: (k5_relat_1(k6_partfun1('#skF_3'), C_14)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_14)) | ~v1_relat_1(C_14) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9608, c_18])).
% 8.79/2.95  tff(c_10030, plain, (![C_521]: (k5_relat_1(k6_partfun1('#skF_3'), C_521)=k5_relat_1('#skF_5', k5_relat_1('#skF_4', C_521)) | ~v1_relat_1(C_521))), inference(demodulation, [status(thm), theory('equality')], [c_238, c_239, c_9744])).
% 8.79/2.95  tff(c_9521, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_429, c_9497])).
% 8.79/2.95  tff(c_9538, plain, (k5_relat_1(k6_partfun1('#skF_3'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_239, c_102, c_86, c_6952, c_9521])).
% 8.79/2.95  tff(c_10039, plain, (k5_relat_1('#skF_5', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_10030, c_9538])).
% 8.79/2.95  tff(c_10117, plain, (k2_funct_1('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_6952, c_8010, c_7313, c_10039])).
% 8.79/2.95  tff(c_10119, plain, $false, inference(negUnitSimplification, [status(thm)], [c_80, c_10117])).
% 8.79/2.95  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.79/2.95  
% 8.79/2.95  Inference rules
% 8.79/2.95  ----------------------
% 8.79/2.95  #Ref     : 0
% 8.79/2.95  #Sup     : 2150
% 8.79/2.95  #Fact    : 0
% 8.79/2.95  #Define  : 0
% 8.79/2.95  #Split   : 34
% 8.79/2.95  #Chain   : 0
% 8.79/2.95  #Close   : 0
% 8.79/2.95  
% 8.79/2.95  Ordering : KBO
% 8.79/2.95  
% 8.79/2.95  Simplification rules
% 8.79/2.95  ----------------------
% 8.79/2.95  #Subsume      : 79
% 8.79/2.95  #Demod        : 3446
% 8.79/2.95  #Tautology    : 1068
% 8.79/2.95  #SimpNegUnit  : 90
% 8.79/2.95  #BackRed      : 113
% 8.79/2.95  
% 8.79/2.95  #Partial instantiations: 0
% 8.79/2.95  #Strategies tried      : 1
% 8.79/2.95  
% 8.79/2.95  Timing (in seconds)
% 8.79/2.95  ----------------------
% 8.79/2.95  Preprocessing        : 0.39
% 8.79/2.95  Parsing              : 0.20
% 8.79/2.95  CNF conversion       : 0.03
% 8.79/2.95  Main loop            : 1.75
% 8.79/2.95  Inferencing          : 0.56
% 8.79/2.95  Reduction            : 0.70
% 8.79/2.95  Demodulation         : 0.53
% 8.79/2.95  BG Simplification    : 0.08
% 8.79/2.95  Subsumption          : 0.30
% 8.79/2.95  Abstraction          : 0.08
% 8.79/2.95  MUC search           : 0.00
% 8.79/2.95  Cooper               : 0.00
% 8.79/2.95  Total                : 2.19
% 8.79/2.95  Index Insertion      : 0.00
% 8.79/2.95  Index Deletion       : 0.00
% 8.79/2.95  Index Matching       : 0.00
% 8.79/2.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
