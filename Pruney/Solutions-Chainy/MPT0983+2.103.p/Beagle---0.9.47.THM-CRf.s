%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:16 EST 2020

% Result     : Theorem 7.57s
% Output     : CNFRefutation 8.02s
% Verified   : 
% Statistics : Number of formulae       :  223 (1917 expanded)
%              Number of leaves         :   46 ( 628 expanded)
%              Depth                    :   13
%              Number of atoms          :  406 (5380 expanded)
%              Number of equality atoms :  103 (1438 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_165,negated_conjecture,(
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

tff(f_106,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_64,axiom,(
    ! [A] : v2_funct_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

tff(f_100,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_104,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_145,axiom,(
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

tff(f_68,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_123,axiom,(
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

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A) )
     => ( v2_funct_2(B,A)
      <=> k2_relat_1(B) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_funct_2)).

tff(c_62,plain,
    ( ~ v2_funct_2('#skF_5','#skF_2')
    | ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_105,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_70,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_68,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_66,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_54,plain,(
    ! [A_37] : k6_relat_1(A_37) = k6_partfun1(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32,plain,(
    ! [A_17] : v2_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_17] : v2_funct_1(k6_partfun1(A_17)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_32])).

tff(c_46,plain,(
    ! [D_33,A_30,C_32,B_31,E_34,F_35] :
      ( m1_subset_1(k1_partfun1(A_30,B_31,C_32,D_33,E_34,F_35),k1_zfmisc_1(k2_zfmisc_1(A_30,D_33)))
      | ~ m1_subset_1(F_35,k1_zfmisc_1(k2_zfmisc_1(C_32,D_33)))
      | ~ v1_funct_1(F_35)
      | ~ m1_subset_1(E_34,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31)))
      | ~ v1_funct_1(E_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_52,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_862,plain,(
    ! [D_174,C_175,A_176,B_177] :
      ( D_174 = C_175
      | ~ r2_relset_1(A_176,B_177,C_175,D_174)
      | ~ m1_subset_1(D_174,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177)))
      | ~ m1_subset_1(C_175,k1_zfmisc_1(k2_zfmisc_1(A_176,B_177))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_874,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_862])).

tff(c_896,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_874])).

tff(c_918,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_896])).

tff(c_1339,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_918])).

tff(c_1346,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_1339])).

tff(c_1347,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_896])).

tff(c_1847,plain,(
    ! [A_326,E_323,B_327,C_324,D_325] :
      ( k1_xboole_0 = C_324
      | v2_funct_1(D_325)
      | ~ v2_funct_1(k1_partfun1(A_326,B_327,B_327,C_324,D_325,E_323))
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(B_327,C_324)))
      | ~ v1_funct_2(E_323,B_327,C_324)
      | ~ v1_funct_1(E_323)
      | ~ m1_subset_1(D_325,k1_zfmisc_1(k2_zfmisc_1(A_326,B_327)))
      | ~ v1_funct_2(D_325,A_326,B_327)
      | ~ v1_funct_1(D_325) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_1849,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1347,c_1847])).

tff(c_1851,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_66,c_77,c_1849])).

tff(c_1852,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_1851])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1885,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_8])).

tff(c_18,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1884,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1852,c_1852,c_18])).

tff(c_486,plain,(
    ! [C_110,B_111,A_112] :
      ( ~ v1_xboole_0(C_110)
      | ~ m1_subset_1(B_111,k1_zfmisc_1(C_110))
      | ~ r2_hidden(A_112,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_502,plain,(
    ! [A_112] :
      ( ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2'))
      | ~ r2_hidden(A_112,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_66,c_486])).

tff(c_533,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_502])).

tff(c_1996,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1884,c_533])).

tff(c_2002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_1996])).

tff(c_2004,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_502])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2251,plain,(
    ! [B_361,A_362,A_363] :
      ( ~ v1_xboole_0(B_361)
      | ~ r2_hidden(A_362,A_363)
      | ~ r1_tarski(A_363,B_361) ) ),
    inference(resolution,[status(thm)],[c_24,c_486])).

tff(c_2255,plain,(
    ! [B_364,A_365,B_366] :
      ( ~ v1_xboole_0(B_364)
      | ~ r1_tarski(A_365,B_364)
      | r1_tarski(A_365,B_366) ) ),
    inference(resolution,[status(thm)],[c_6,c_2251])).

tff(c_2278,plain,(
    ! [B_369,B_370] :
      ( ~ v1_xboole_0(B_369)
      | r1_tarski(B_369,B_370) ) ),
    inference(resolution,[status(thm)],[c_14,c_2255])).

tff(c_117,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_128,plain,(
    r1_tarski('#skF_5',k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_117])).

tff(c_170,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,
    ( k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5'
    | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_128,c_170])).

tff(c_427,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_2'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_2302,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_2278,c_427])).

tff(c_2314,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_2302])).

tff(c_2315,plain,(
    k2_zfmisc_1('#skF_3','#skF_2') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_2318,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2315,c_66])).

tff(c_2790,plain,(
    ! [D_447,C_448,A_449,B_450] :
      ( D_447 = C_448
      | ~ r2_relset_1(A_449,B_450,C_448,D_447)
      | ~ m1_subset_1(D_447,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450)))
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_449,B_450))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_2804,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_2790])).

tff(c_2829,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_2804])).

tff(c_2865,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2829])).

tff(c_3131,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_2865])).

tff(c_3138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_2318,c_2315,c_3131])).

tff(c_3139,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_2829])).

tff(c_3610,plain,(
    ! [E_566,D_568,A_569,C_567,B_570] :
      ( k1_xboole_0 = C_567
      | v2_funct_1(D_568)
      | ~ v2_funct_1(k1_partfun1(A_569,B_570,B_570,C_567,D_568,E_566))
      | ~ m1_subset_1(E_566,k1_zfmisc_1(k2_zfmisc_1(B_570,C_567)))
      | ~ v1_funct_2(E_566,B_570,C_567)
      | ~ v1_funct_1(E_566)
      | ~ m1_subset_1(D_568,k1_zfmisc_1(k2_zfmisc_1(A_569,B_570)))
      | ~ v1_funct_2(D_568,A_569,B_570)
      | ~ v1_funct_1(D_568) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_3612,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3139,c_3610])).

tff(c_3614,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_72,c_70,c_68,c_2318,c_2315,c_77,c_3612])).

tff(c_3615,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_3614])).

tff(c_16,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2323,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 != '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2315,c_16])).

tff(c_2342,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2323])).

tff(c_3641,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_2342])).

tff(c_3648,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3615,c_3615,c_18])).

tff(c_3768,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3648,c_2315])).

tff(c_3770,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3641,c_3768])).

tff(c_3772,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_3771,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_3809,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_3772,c_3771])).

tff(c_3810,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3809])).

tff(c_3780,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_8])).

tff(c_3814,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_3780])).

tff(c_3816,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_3810,c_2318])).

tff(c_3998,plain,(
    ! [C_599,B_600,A_601] :
      ( ~ v1_xboole_0(C_599)
      | ~ m1_subset_1(B_600,k1_zfmisc_1(C_599))
      | ~ r2_hidden(A_601,B_600) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4000,plain,(
    ! [A_601] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_601,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_3816,c_3998])).

tff(c_4015,plain,(
    ! [A_602] : ~ r2_hidden(A_602,'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3814,c_4000])).

tff(c_4020,plain,(
    ! [B_2] : r1_tarski('#skF_2',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4015])).

tff(c_20,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_3778,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_3772,c_20])).

tff(c_3865,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_2',B_9) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3810,c_3810,c_3778])).

tff(c_129,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_117])).

tff(c_183,plain,
    ( k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_129,c_170])).

tff(c_2340,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_183])).

tff(c_3866,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3865,c_2340])).

tff(c_4029,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4020,c_3866])).

tff(c_4030,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3809])).

tff(c_4035,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_3780])).

tff(c_4037,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_4030,c_2318])).

tff(c_4250,plain,(
    ! [C_628,B_629,A_630] :
      ( ~ v1_xboole_0(C_628)
      | ~ m1_subset_1(B_629,k1_zfmisc_1(C_628))
      | ~ r2_hidden(A_630,B_629) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4252,plain,(
    ! [A_630] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_630,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_4037,c_4250])).

tff(c_4267,plain,(
    ! [A_631] : ~ r2_hidden(A_631,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4035,c_4252])).

tff(c_4272,plain,(
    ! [B_2] : r1_tarski('#skF_3',B_2) ),
    inference(resolution,[status(thm)],[c_6,c_4267])).

tff(c_3779,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3772,c_3772,c_18])).

tff(c_4087,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4030,c_4030,c_3779])).

tff(c_4088,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4087,c_2340])).

tff(c_4281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4272,c_4088])).

tff(c_4282,plain,(
    k2_zfmisc_1('#skF_2','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_183])).

tff(c_4285,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4282,c_72])).

tff(c_4985,plain,(
    ! [C_742,F_744,B_743,A_745,D_747,E_746] :
      ( m1_subset_1(k1_partfun1(A_745,B_743,C_742,D_747,E_746,F_744),k1_zfmisc_1(k2_zfmisc_1(A_745,D_747)))
      | ~ m1_subset_1(F_744,k1_zfmisc_1(k2_zfmisc_1(C_742,D_747)))
      | ~ v1_funct_1(F_744)
      | ~ m1_subset_1(E_746,k1_zfmisc_1(k2_zfmisc_1(A_745,B_743)))
      | ~ v1_funct_1(E_746) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_4765,plain,(
    ! [D_708,C_709,A_710,B_711] :
      ( D_708 = C_709
      | ~ r2_relset_1(A_710,B_711,C_709,D_708)
      | ~ m1_subset_1(D_708,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711)))
      | ~ m1_subset_1(C_709,k1_zfmisc_1(k2_zfmisc_1(A_710,B_711))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_4779,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_4765])).

tff(c_4804,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_4779])).

tff(c_4826,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_4804])).

tff(c_4988,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4985,c_4826])).

tff(c_5019,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4285,c_4282,c_70,c_2318,c_2315,c_4988])).

tff(c_5020,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_4804])).

tff(c_5587,plain,(
    ! [D_829,C_828,E_827,A_830,B_831] :
      ( k1_xboole_0 = C_828
      | v2_funct_1(D_829)
      | ~ v2_funct_1(k1_partfun1(A_830,B_831,B_831,C_828,D_829,E_827))
      | ~ m1_subset_1(E_827,k1_zfmisc_1(k2_zfmisc_1(B_831,C_828)))
      | ~ v1_funct_2(E_827,B_831,C_828)
      | ~ v1_funct_1(E_827)
      | ~ m1_subset_1(D_829,k1_zfmisc_1(k2_zfmisc_1(A_830,B_831)))
      | ~ v1_funct_2(D_829,A_830,B_831)
      | ~ v1_funct_1(D_829) ) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_5589,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4')
    | ~ v2_funct_1(k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5020,c_5587])).

tff(c_5591,plain,
    ( k1_xboole_0 = '#skF_2'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_4285,c_4282,c_70,c_68,c_2318,c_2315,c_77,c_5589])).

tff(c_5592,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_5591])).

tff(c_4308,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2323])).

tff(c_5618,plain,(
    '#skF_5' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5592,c_4308])).

tff(c_5625,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5592,c_5592,c_18])).

tff(c_5759,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5625,c_2315])).

tff(c_5761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5618,c_5759])).

tff(c_5763,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_5762,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2323])).

tff(c_5836,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5763,c_5762])).

tff(c_5837,plain,(
    '#skF_5' = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_5836])).

tff(c_4290,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4282,c_16])).

tff(c_5810,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_5' = '#skF_2'
    | '#skF_5' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5763,c_5763,c_4290])).

tff(c_5811,plain,(
    '#skF_5' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5810])).

tff(c_5841,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_5811])).

tff(c_5769,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_5',B_9) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5763,c_20])).

tff(c_5935,plain,(
    ! [B_855] : k2_zfmisc_1('#skF_2',B_855) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5837,c_5837,c_5769])).

tff(c_5944,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_5935,c_4282])).

tff(c_5963,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5841,c_5944])).

tff(c_5964,plain,(
    '#skF_5' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5836])).

tff(c_5969,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5964,c_5811])).

tff(c_5770,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_5763,c_18])).

tff(c_6019,plain,(
    ! [A_859] : k2_zfmisc_1(A_859,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5964,c_5964,c_5770])).

tff(c_6025,plain,(
    '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_6019,c_4282])).

tff(c_6040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5969,c_6025])).

tff(c_6042,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5810])).

tff(c_277,plain,(
    ! [C_81,B_82,A_83] :
      ( ~ v1_xboole_0(C_81)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(C_81))
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_344,plain,(
    ! [B_89,A_90,A_91] :
      ( ~ v1_xboole_0(B_89)
      | ~ r2_hidden(A_90,A_91)
      | ~ r1_tarski(A_91,B_89) ) ),
    inference(resolution,[status(thm)],[c_24,c_277])).

tff(c_352,plain,(
    ! [B_95,A_96,B_97] :
      ( ~ v1_xboole_0(B_95)
      | ~ r1_tarski(A_96,B_95)
      | r1_tarski(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_344])).

tff(c_369,plain,(
    ! [B_98,B_99] :
      ( ~ v1_xboole_0(B_98)
      | r1_tarski(B_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_14,c_352])).

tff(c_130,plain,(
    ! [A_60] : m1_subset_1(k6_partfun1(A_60),k1_zfmisc_1(k2_zfmisc_1(A_60,A_60))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_137,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_130])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_146,plain,(
    r1_tarski(k6_partfun1(k1_xboole_0),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_137,c_22])).

tff(c_182,plain,
    ( k6_partfun1(k1_xboole_0) = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_146,c_170])).

tff(c_189,plain,(
    ~ r1_tarski(k1_xboole_0,k6_partfun1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_392,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_369,c_189])).

tff(c_404,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_392])).

tff(c_405,plain,(
    k6_partfun1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_421,plain,(
    v2_funct_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_405,c_77])).

tff(c_5766,plain,(
    v2_funct_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5763,c_421])).

tff(c_6044,plain,(
    v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6042,c_5766])).

tff(c_6053,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_6044])).

tff(c_6054,plain,(
    ~ v2_funct_2('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_6121,plain,(
    ! [C_872,A_873,B_874] :
      ( v1_relat_1(C_872)
      | ~ m1_subset_1(C_872,k1_zfmisc_1(k2_zfmisc_1(A_873,B_874))) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6142,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6121])).

tff(c_6523,plain,(
    ! [A_927,B_928,D_929] :
      ( r2_relset_1(A_927,B_928,D_929,D_929)
      | ~ m1_subset_1(D_929,k1_zfmisc_1(k2_zfmisc_1(A_927,B_928))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6538,plain,(
    ! [A_36] : r2_relset_1(A_36,A_36,k6_partfun1(A_36),k6_partfun1(A_36)) ),
    inference(resolution,[status(thm)],[c_52,c_6523])).

tff(c_6616,plain,(
    ! [A_941,B_942,C_943] :
      ( k2_relset_1(A_941,B_942,C_943) = k2_relat_1(C_943)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_941,B_942))) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6639,plain,(
    k2_relset_1('#skF_3','#skF_2','#skF_5') = k2_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_6616])).

tff(c_6711,plain,(
    ! [D_951,C_952,A_953,B_954] :
      ( D_951 = C_952
      | ~ r2_relset_1(A_953,B_954,C_952,D_951)
      | ~ m1_subset_1(D_951,k1_zfmisc_1(k2_zfmisc_1(A_953,B_954)))
      | ~ m1_subset_1(C_952,k1_zfmisc_1(k2_zfmisc_1(A_953,B_954))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_6721,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_64,c_6711])).

tff(c_6740,plain,
    ( k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_6721])).

tff(c_6754,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_6740])).

tff(c_7088,plain,
    ( ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_6754])).

tff(c_7095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_70,c_66,c_7088])).

tff(c_7096,plain,(
    k1_partfun1('#skF_2','#skF_3','#skF_3','#skF_2','#skF_4','#skF_5') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_6740])).

tff(c_7623,plain,(
    ! [A_1109,B_1110,C_1111,D_1112] :
      ( k2_relset_1(A_1109,B_1110,C_1111) = B_1110
      | ~ r2_relset_1(B_1110,B_1110,k1_partfun1(B_1110,A_1109,A_1109,B_1110,D_1112,C_1111),k6_partfun1(B_1110))
      | ~ m1_subset_1(D_1112,k1_zfmisc_1(k2_zfmisc_1(B_1110,A_1109)))
      | ~ v1_funct_2(D_1112,B_1110,A_1109)
      | ~ v1_funct_1(D_1112)
      | ~ m1_subset_1(C_1111,k1_zfmisc_1(k2_zfmisc_1(A_1109,B_1110)))
      | ~ v1_funct_2(C_1111,A_1109,B_1110)
      | ~ v1_funct_1(C_1111) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_7626,plain,
    ( k2_relset_1('#skF_3','#skF_2','#skF_5') = '#skF_2'
    | ~ r2_relset_1('#skF_2','#skF_2',k6_partfun1('#skF_2'),k6_partfun1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2('#skF_5','#skF_3','#skF_2')
    | ~ v1_funct_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7096,c_7623])).

tff(c_7631,plain,(
    k2_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_66,c_76,c_74,c_72,c_6538,c_6639,c_7626])).

tff(c_6431,plain,(
    ! [B_911,A_912] :
      ( v5_relat_1(B_911,A_912)
      | ~ r1_tarski(k2_relat_1(B_911),A_912)
      | ~ v1_relat_1(B_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6440,plain,(
    ! [B_911] :
      ( v5_relat_1(B_911,k2_relat_1(B_911))
      | ~ v1_relat_1(B_911) ) ),
    inference(resolution,[status(thm)],[c_14,c_6431])).

tff(c_6464,plain,(
    ! [B_920] :
      ( v2_funct_2(B_920,k2_relat_1(B_920))
      | ~ v5_relat_1(B_920,k2_relat_1(B_920))
      | ~ v1_relat_1(B_920) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_6468,plain,(
    ! [B_911] :
      ( v2_funct_2(B_911,k2_relat_1(B_911))
      | ~ v1_relat_1(B_911) ) ),
    inference(resolution,[status(thm)],[c_6440,c_6464])).

tff(c_7642,plain,
    ( v2_funct_2('#skF_5','#skF_2')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7631,c_6468])).

tff(c_7662,plain,(
    v2_funct_2('#skF_5','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6142,c_7642])).

tff(c_7664,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6054,c_7662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:33:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.57/2.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.66  
% 7.57/2.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.57/2.67  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v2_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.57/2.67  
% 7.57/2.67  %Foreground sorts:
% 7.57/2.67  
% 7.57/2.67  
% 7.57/2.67  %Background operators:
% 7.57/2.67  
% 7.57/2.67  
% 7.57/2.67  %Foreground operators:
% 7.57/2.67  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 7.57/2.67  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.57/2.67  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.57/2.67  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 7.57/2.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.57/2.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.57/2.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.57/2.67  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.57/2.67  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.57/2.67  tff('#skF_5', type, '#skF_5': $i).
% 7.57/2.67  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.57/2.67  tff('#skF_2', type, '#skF_2': $i).
% 7.57/2.67  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.57/2.67  tff('#skF_3', type, '#skF_3': $i).
% 7.57/2.67  tff(v2_funct_2, type, v2_funct_2: ($i * $i) > $o).
% 7.57/2.67  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.57/2.67  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.57/2.67  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.57/2.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.57/2.67  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.57/2.67  tff('#skF_4', type, '#skF_4': $i).
% 7.57/2.67  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 7.57/2.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.57/2.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.57/2.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.57/2.67  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.57/2.67  
% 8.02/2.70  tff(f_165, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A)) => (v2_funct_1(C) & v2_funct_2(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_funct_2)).
% 8.02/2.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 8.02/2.70  tff(f_106, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.02/2.70  tff(f_64, axiom, (![A]: v2_funct_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_funct_1)).
% 8.02/2.70  tff(f_100, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.02/2.70  tff(f_104, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.02/2.70  tff(f_80, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.02/2.70  tff(f_145, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 8.02/2.70  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 8.02/2.70  tff(f_45, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.02/2.70  tff(f_56, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 8.02/2.70  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.02/2.70  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.02/2.70  tff(f_68, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.02/2.70  tff(f_72, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.02/2.70  tff(f_123, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 8.02/2.70  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.02/2.70  tff(f_88, axiom, (![A, B]: ((v1_relat_1(B) & v5_relat_1(B, A)) => (v2_funct_2(B, A) <=> (k2_relat_1(B) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_funct_2)).
% 8.02/2.70  tff(c_62, plain, (~v2_funct_2('#skF_5', '#skF_2') | ~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_105, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_62])).
% 8.02/2.70  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 8.02/2.70  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_70, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_68, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_66, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_54, plain, (![A_37]: (k6_relat_1(A_37)=k6_partfun1(A_37))), inference(cnfTransformation, [status(thm)], [f_106])).
% 8.02/2.70  tff(c_32, plain, (![A_17]: (v2_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.02/2.70  tff(c_77, plain, (![A_17]: (v2_funct_1(k6_partfun1(A_17)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_32])).
% 8.02/2.70  tff(c_46, plain, (![D_33, A_30, C_32, B_31, E_34, F_35]: (m1_subset_1(k1_partfun1(A_30, B_31, C_32, D_33, E_34, F_35), k1_zfmisc_1(k2_zfmisc_1(A_30, D_33))) | ~m1_subset_1(F_35, k1_zfmisc_1(k2_zfmisc_1(C_32, D_33))) | ~v1_funct_1(F_35) | ~m1_subset_1(E_34, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))) | ~v1_funct_1(E_34))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.02/2.70  tff(c_52, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.02/2.70  tff(c_64, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_165])).
% 8.02/2.70  tff(c_862, plain, (![D_174, C_175, A_176, B_177]: (D_174=C_175 | ~r2_relset_1(A_176, B_177, C_175, D_174) | ~m1_subset_1(D_174, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))) | ~m1_subset_1(C_175, k1_zfmisc_1(k2_zfmisc_1(A_176, B_177))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.70  tff(c_874, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_862])).
% 8.02/2.70  tff(c_896, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_874])).
% 8.02/2.70  tff(c_918, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_896])).
% 8.02/2.70  tff(c_1339, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_918])).
% 8.02/2.70  tff(c_1346, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_1339])).
% 8.02/2.70  tff(c_1347, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_896])).
% 8.02/2.70  tff(c_1847, plain, (![A_326, E_323, B_327, C_324, D_325]: (k1_xboole_0=C_324 | v2_funct_1(D_325) | ~v2_funct_1(k1_partfun1(A_326, B_327, B_327, C_324, D_325, E_323)) | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(B_327, C_324))) | ~v1_funct_2(E_323, B_327, C_324) | ~v1_funct_1(E_323) | ~m1_subset_1(D_325, k1_zfmisc_1(k2_zfmisc_1(A_326, B_327))) | ~v1_funct_2(D_325, A_326, B_327) | ~v1_funct_1(D_325))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.02/2.70  tff(c_1849, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1347, c_1847])).
% 8.02/2.70  tff(c_1851, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_66, c_77, c_1849])).
% 8.02/2.70  tff(c_1852, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_105, c_1851])).
% 8.02/2.70  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.02/2.70  tff(c_1885, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_8])).
% 8.02/2.70  tff(c_18, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.70  tff(c_1884, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1852, c_1852, c_18])).
% 8.02/2.70  tff(c_486, plain, (![C_110, B_111, A_112]: (~v1_xboole_0(C_110) | ~m1_subset_1(B_111, k1_zfmisc_1(C_110)) | ~r2_hidden(A_112, B_111))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.70  tff(c_502, plain, (![A_112]: (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2')) | ~r2_hidden(A_112, '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_486])).
% 8.02/2.70  tff(c_533, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitLeft, [status(thm)], [c_502])).
% 8.02/2.70  tff(c_1996, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1884, c_533])).
% 8.02/2.70  tff(c_2002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1885, c_1996])).
% 8.02/2.70  tff(c_2004, plain, (v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_502])).
% 8.02/2.70  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.02/2.70  tff(c_24, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.02/2.70  tff(c_2251, plain, (![B_361, A_362, A_363]: (~v1_xboole_0(B_361) | ~r2_hidden(A_362, A_363) | ~r1_tarski(A_363, B_361))), inference(resolution, [status(thm)], [c_24, c_486])).
% 8.02/2.70  tff(c_2255, plain, (![B_364, A_365, B_366]: (~v1_xboole_0(B_364) | ~r1_tarski(A_365, B_364) | r1_tarski(A_365, B_366))), inference(resolution, [status(thm)], [c_6, c_2251])).
% 8.02/2.70  tff(c_2278, plain, (![B_369, B_370]: (~v1_xboole_0(B_369) | r1_tarski(B_369, B_370))), inference(resolution, [status(thm)], [c_14, c_2255])).
% 8.02/2.70  tff(c_117, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.02/2.70  tff(c_128, plain, (r1_tarski('#skF_5', k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_117])).
% 8.02/2.70  tff(c_170, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.02/2.70  tff(c_184, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5' | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(resolution, [status(thm)], [c_128, c_170])).
% 8.02/2.70  tff(c_427, plain, (~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_2'), '#skF_5')), inference(splitLeft, [status(thm)], [c_184])).
% 8.02/2.70  tff(c_2302, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_2278, c_427])).
% 8.02/2.70  tff(c_2314, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2004, c_2302])).
% 8.02/2.70  tff(c_2315, plain, (k2_zfmisc_1('#skF_3', '#skF_2')='#skF_5'), inference(splitRight, [status(thm)], [c_184])).
% 8.02/2.70  tff(c_2318, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2315, c_66])).
% 8.02/2.70  tff(c_2790, plain, (![D_447, C_448, A_449, B_450]: (D_447=C_448 | ~r2_relset_1(A_449, B_450, C_448, D_447) | ~m1_subset_1(D_447, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_449, B_450))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.70  tff(c_2804, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_2790])).
% 8.02/2.70  tff(c_2829, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_2804])).
% 8.02/2.70  tff(c_2865, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2829])).
% 8.02/2.70  tff(c_3131, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_2865])).
% 8.02/2.70  tff(c_3138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_2318, c_2315, c_3131])).
% 8.02/2.70  tff(c_3139, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_2829])).
% 8.02/2.70  tff(c_3610, plain, (![E_566, D_568, A_569, C_567, B_570]: (k1_xboole_0=C_567 | v2_funct_1(D_568) | ~v2_funct_1(k1_partfun1(A_569, B_570, B_570, C_567, D_568, E_566)) | ~m1_subset_1(E_566, k1_zfmisc_1(k2_zfmisc_1(B_570, C_567))) | ~v1_funct_2(E_566, B_570, C_567) | ~v1_funct_1(E_566) | ~m1_subset_1(D_568, k1_zfmisc_1(k2_zfmisc_1(A_569, B_570))) | ~v1_funct_2(D_568, A_569, B_570) | ~v1_funct_1(D_568))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.02/2.70  tff(c_3612, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3139, c_3610])).
% 8.02/2.70  tff(c_3614, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_72, c_70, c_68, c_2318, c_2315, c_77, c_3612])).
% 8.02/2.70  tff(c_3615, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_105, c_3614])).
% 8.02/2.70  tff(c_16, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.70  tff(c_2323, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k1_xboole_0!='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_2315, c_16])).
% 8.02/2.70  tff(c_2342, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_3641, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_2342])).
% 8.02/2.70  tff(c_3648, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3615, c_3615, c_18])).
% 8.02/2.70  tff(c_3768, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3648, c_2315])).
% 8.02/2.70  tff(c_3770, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3641, c_3768])).
% 8.02/2.70  tff(c_3772, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_3771, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_3809, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_3772, c_3771])).
% 8.02/2.70  tff(c_3810, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_3809])).
% 8.02/2.70  tff(c_3780, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_8])).
% 8.02/2.70  tff(c_3814, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3810, c_3780])).
% 8.02/2.70  tff(c_3816, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3810, c_3810, c_2318])).
% 8.02/2.70  tff(c_3998, plain, (![C_599, B_600, A_601]: (~v1_xboole_0(C_599) | ~m1_subset_1(B_600, k1_zfmisc_1(C_599)) | ~r2_hidden(A_601, B_600))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.70  tff(c_4000, plain, (![A_601]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_601, '#skF_2'))), inference(resolution, [status(thm)], [c_3816, c_3998])).
% 8.02/2.70  tff(c_4015, plain, (![A_602]: (~r2_hidden(A_602, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_3814, c_4000])).
% 8.02/2.70  tff(c_4020, plain, (![B_2]: (r1_tarski('#skF_2', B_2))), inference(resolution, [status(thm)], [c_6, c_4015])).
% 8.02/2.70  tff(c_20, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.02/2.70  tff(c_3778, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_3772, c_20])).
% 8.02/2.70  tff(c_3865, plain, (![B_9]: (k2_zfmisc_1('#skF_2', B_9)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3810, c_3810, c_3778])).
% 8.02/2.70  tff(c_129, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_117])).
% 8.02/2.70  tff(c_183, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_129, c_170])).
% 8.02/2.70  tff(c_2340, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_183])).
% 8.02/2.70  tff(c_3866, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3865, c_2340])).
% 8.02/2.70  tff(c_4029, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4020, c_3866])).
% 8.02/2.70  tff(c_4030, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_3809])).
% 8.02/2.70  tff(c_4035, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4030, c_3780])).
% 8.02/2.70  tff(c_4037, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4030, c_4030, c_2318])).
% 8.02/2.70  tff(c_4250, plain, (![C_628, B_629, A_630]: (~v1_xboole_0(C_628) | ~m1_subset_1(B_629, k1_zfmisc_1(C_628)) | ~r2_hidden(A_630, B_629))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.70  tff(c_4252, plain, (![A_630]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_630, '#skF_3'))), inference(resolution, [status(thm)], [c_4037, c_4250])).
% 8.02/2.70  tff(c_4267, plain, (![A_631]: (~r2_hidden(A_631, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4035, c_4252])).
% 8.02/2.70  tff(c_4272, plain, (![B_2]: (r1_tarski('#skF_3', B_2))), inference(resolution, [status(thm)], [c_6, c_4267])).
% 8.02/2.70  tff(c_3779, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3772, c_3772, c_18])).
% 8.02/2.70  tff(c_4087, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4030, c_4030, c_3779])).
% 8.02/2.70  tff(c_4088, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4087, c_2340])).
% 8.02/2.70  tff(c_4281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4272, c_4088])).
% 8.02/2.70  tff(c_4282, plain, (k2_zfmisc_1('#skF_2', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_183])).
% 8.02/2.70  tff(c_4285, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4282, c_72])).
% 8.02/2.70  tff(c_4985, plain, (![C_742, F_744, B_743, A_745, D_747, E_746]: (m1_subset_1(k1_partfun1(A_745, B_743, C_742, D_747, E_746, F_744), k1_zfmisc_1(k2_zfmisc_1(A_745, D_747))) | ~m1_subset_1(F_744, k1_zfmisc_1(k2_zfmisc_1(C_742, D_747))) | ~v1_funct_1(F_744) | ~m1_subset_1(E_746, k1_zfmisc_1(k2_zfmisc_1(A_745, B_743))) | ~v1_funct_1(E_746))), inference(cnfTransformation, [status(thm)], [f_100])).
% 8.02/2.70  tff(c_4765, plain, (![D_708, C_709, A_710, B_711]: (D_708=C_709 | ~r2_relset_1(A_710, B_711, C_709, D_708) | ~m1_subset_1(D_708, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))) | ~m1_subset_1(C_709, k1_zfmisc_1(k2_zfmisc_1(A_710, B_711))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.70  tff(c_4779, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_4765])).
% 8.02/2.70  tff(c_4804, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_4779])).
% 8.02/2.70  tff(c_4826, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_4804])).
% 8.02/2.70  tff(c_4988, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_4985, c_4826])).
% 8.02/2.70  tff(c_5019, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_4285, c_4282, c_70, c_2318, c_2315, c_4988])).
% 8.02/2.70  tff(c_5020, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_4804])).
% 8.02/2.70  tff(c_5587, plain, (![D_829, C_828, E_827, A_830, B_831]: (k1_xboole_0=C_828 | v2_funct_1(D_829) | ~v2_funct_1(k1_partfun1(A_830, B_831, B_831, C_828, D_829, E_827)) | ~m1_subset_1(E_827, k1_zfmisc_1(k2_zfmisc_1(B_831, C_828))) | ~v1_funct_2(E_827, B_831, C_828) | ~v1_funct_1(E_827) | ~m1_subset_1(D_829, k1_zfmisc_1(k2_zfmisc_1(A_830, B_831))) | ~v1_funct_2(D_829, A_830, B_831) | ~v1_funct_1(D_829))), inference(cnfTransformation, [status(thm)], [f_145])).
% 8.02/2.70  tff(c_5589, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4') | ~v2_funct_1(k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5020, c_5587])).
% 8.02/2.70  tff(c_5591, plain, (k1_xboole_0='#skF_2' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_4285, c_4282, c_70, c_68, c_2318, c_2315, c_77, c_5589])).
% 8.02/2.70  tff(c_5592, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_105, c_5591])).
% 8.02/2.70  tff(c_4308, plain, (k1_xboole_0!='#skF_5'), inference(splitLeft, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_5618, plain, ('#skF_5'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5592, c_4308])).
% 8.02/2.70  tff(c_5625, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5592, c_5592, c_18])).
% 8.02/2.70  tff(c_5759, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5625, c_2315])).
% 8.02/2.70  tff(c_5761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5618, c_5759])).
% 8.02/2.70  tff(c_5763, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_5762, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2323])).
% 8.02/2.70  tff(c_5836, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5763, c_5762])).
% 8.02/2.70  tff(c_5837, plain, ('#skF_5'='#skF_2'), inference(splitLeft, [status(thm)], [c_5836])).
% 8.02/2.70  tff(c_4290, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_4282, c_16])).
% 8.02/2.70  tff(c_5810, plain, ('#skF_5'='#skF_3' | '#skF_5'='#skF_2' | '#skF_5'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5763, c_5763, c_4290])).
% 8.02/2.70  tff(c_5811, plain, ('#skF_5'!='#skF_4'), inference(splitLeft, [status(thm)], [c_5810])).
% 8.02/2.70  tff(c_5841, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5837, c_5811])).
% 8.02/2.70  tff(c_5769, plain, (![B_9]: (k2_zfmisc_1('#skF_5', B_9)='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5763, c_20])).
% 8.02/2.70  tff(c_5935, plain, (![B_855]: (k2_zfmisc_1('#skF_2', B_855)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5837, c_5837, c_5769])).
% 8.02/2.70  tff(c_5944, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_5935, c_4282])).
% 8.02/2.70  tff(c_5963, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5841, c_5944])).
% 8.02/2.70  tff(c_5964, plain, ('#skF_5'='#skF_3'), inference(splitRight, [status(thm)], [c_5836])).
% 8.02/2.70  tff(c_5969, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5964, c_5811])).
% 8.02/2.70  tff(c_5770, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_5763, c_18])).
% 8.02/2.70  tff(c_6019, plain, (![A_859]: (k2_zfmisc_1(A_859, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5964, c_5964, c_5770])).
% 8.02/2.70  tff(c_6025, plain, ('#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_6019, c_4282])).
% 8.02/2.70  tff(c_6040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5969, c_6025])).
% 8.02/2.70  tff(c_6042, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_5810])).
% 8.02/2.70  tff(c_277, plain, (![C_81, B_82, A_83]: (~v1_xboole_0(C_81) | ~m1_subset_1(B_82, k1_zfmisc_1(C_81)) | ~r2_hidden(A_83, B_82))), inference(cnfTransformation, [status(thm)], [f_56])).
% 8.02/2.70  tff(c_344, plain, (![B_89, A_90, A_91]: (~v1_xboole_0(B_89) | ~r2_hidden(A_90, A_91) | ~r1_tarski(A_91, B_89))), inference(resolution, [status(thm)], [c_24, c_277])).
% 8.02/2.70  tff(c_352, plain, (![B_95, A_96, B_97]: (~v1_xboole_0(B_95) | ~r1_tarski(A_96, B_95) | r1_tarski(A_96, B_97))), inference(resolution, [status(thm)], [c_6, c_344])).
% 8.02/2.70  tff(c_369, plain, (![B_98, B_99]: (~v1_xboole_0(B_98) | r1_tarski(B_98, B_99))), inference(resolution, [status(thm)], [c_14, c_352])).
% 8.02/2.70  tff(c_130, plain, (![A_60]: (m1_subset_1(k6_partfun1(A_60), k1_zfmisc_1(k2_zfmisc_1(A_60, A_60))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 8.02/2.70  tff(c_137, plain, (m1_subset_1(k6_partfun1(k1_xboole_0), k1_zfmisc_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_130])).
% 8.02/2.70  tff(c_22, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 8.02/2.70  tff(c_146, plain, (r1_tarski(k6_partfun1(k1_xboole_0), k1_xboole_0)), inference(resolution, [status(thm)], [c_137, c_22])).
% 8.02/2.70  tff(c_182, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(resolution, [status(thm)], [c_146, c_170])).
% 8.02/2.70  tff(c_189, plain, (~r1_tarski(k1_xboole_0, k6_partfun1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_182])).
% 8.02/2.70  tff(c_392, plain, (~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_369, c_189])).
% 8.02/2.70  tff(c_404, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_392])).
% 8.02/2.70  tff(c_405, plain, (k6_partfun1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_182])).
% 8.02/2.70  tff(c_421, plain, (v2_funct_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_405, c_77])).
% 8.02/2.70  tff(c_5766, plain, (v2_funct_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_5763, c_421])).
% 8.02/2.70  tff(c_6044, plain, (v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6042, c_5766])).
% 8.02/2.70  tff(c_6053, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_6044])).
% 8.02/2.70  tff(c_6054, plain, (~v2_funct_2('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_62])).
% 8.02/2.70  tff(c_6121, plain, (![C_872, A_873, B_874]: (v1_relat_1(C_872) | ~m1_subset_1(C_872, k1_zfmisc_1(k2_zfmisc_1(A_873, B_874))))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.02/2.70  tff(c_6142, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_6121])).
% 8.02/2.70  tff(c_6523, plain, (![A_927, B_928, D_929]: (r2_relset_1(A_927, B_928, D_929, D_929) | ~m1_subset_1(D_929, k1_zfmisc_1(k2_zfmisc_1(A_927, B_928))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.70  tff(c_6538, plain, (![A_36]: (r2_relset_1(A_36, A_36, k6_partfun1(A_36), k6_partfun1(A_36)))), inference(resolution, [status(thm)], [c_52, c_6523])).
% 8.02/2.70  tff(c_6616, plain, (![A_941, B_942, C_943]: (k2_relset_1(A_941, B_942, C_943)=k2_relat_1(C_943) | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_941, B_942))))), inference(cnfTransformation, [status(thm)], [f_72])).
% 8.02/2.70  tff(c_6639, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')=k2_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_66, c_6616])).
% 8.02/2.70  tff(c_6711, plain, (![D_951, C_952, A_953, B_954]: (D_951=C_952 | ~r2_relset_1(A_953, B_954, C_952, D_951) | ~m1_subset_1(D_951, k1_zfmisc_1(k2_zfmisc_1(A_953, B_954))) | ~m1_subset_1(C_952, k1_zfmisc_1(k2_zfmisc_1(A_953, B_954))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 8.02/2.70  tff(c_6721, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_64, c_6711])).
% 8.02/2.70  tff(c_6740, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_6721])).
% 8.02/2.70  tff(c_6754, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_6740])).
% 8.02/2.70  tff(c_7088, plain, (~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_46, c_6754])).
% 8.02/2.70  tff(c_7095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_70, c_66, c_7088])).
% 8.02/2.70  tff(c_7096, plain, (k1_partfun1('#skF_2', '#skF_3', '#skF_3', '#skF_2', '#skF_4', '#skF_5')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_6740])).
% 8.02/2.70  tff(c_7623, plain, (![A_1109, B_1110, C_1111, D_1112]: (k2_relset_1(A_1109, B_1110, C_1111)=B_1110 | ~r2_relset_1(B_1110, B_1110, k1_partfun1(B_1110, A_1109, A_1109, B_1110, D_1112, C_1111), k6_partfun1(B_1110)) | ~m1_subset_1(D_1112, k1_zfmisc_1(k2_zfmisc_1(B_1110, A_1109))) | ~v1_funct_2(D_1112, B_1110, A_1109) | ~v1_funct_1(D_1112) | ~m1_subset_1(C_1111, k1_zfmisc_1(k2_zfmisc_1(A_1109, B_1110))) | ~v1_funct_2(C_1111, A_1109, B_1110) | ~v1_funct_1(C_1111))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.02/2.70  tff(c_7626, plain, (k2_relset_1('#skF_3', '#skF_2', '#skF_5')='#skF_2' | ~r2_relset_1('#skF_2', '#skF_2', k6_partfun1('#skF_2'), k6_partfun1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2('#skF_5', '#skF_3', '#skF_2') | ~v1_funct_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7096, c_7623])).
% 8.02/2.70  tff(c_7631, plain, (k2_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_66, c_76, c_74, c_72, c_6538, c_6639, c_7626])).
% 8.02/2.70  tff(c_6431, plain, (![B_911, A_912]: (v5_relat_1(B_911, A_912) | ~r1_tarski(k2_relat_1(B_911), A_912) | ~v1_relat_1(B_911))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.02/2.70  tff(c_6440, plain, (![B_911]: (v5_relat_1(B_911, k2_relat_1(B_911)) | ~v1_relat_1(B_911))), inference(resolution, [status(thm)], [c_14, c_6431])).
% 8.02/2.70  tff(c_6464, plain, (![B_920]: (v2_funct_2(B_920, k2_relat_1(B_920)) | ~v5_relat_1(B_920, k2_relat_1(B_920)) | ~v1_relat_1(B_920))), inference(cnfTransformation, [status(thm)], [f_88])).
% 8.02/2.70  tff(c_6468, plain, (![B_911]: (v2_funct_2(B_911, k2_relat_1(B_911)) | ~v1_relat_1(B_911))), inference(resolution, [status(thm)], [c_6440, c_6464])).
% 8.02/2.70  tff(c_7642, plain, (v2_funct_2('#skF_5', '#skF_2') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7631, c_6468])).
% 8.02/2.70  tff(c_7662, plain, (v2_funct_2('#skF_5', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6142, c_7642])).
% 8.02/2.70  tff(c_7664, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6054, c_7662])).
% 8.02/2.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.02/2.70  
% 8.02/2.70  Inference rules
% 8.02/2.70  ----------------------
% 8.02/2.70  #Ref     : 0
% 8.02/2.70  #Sup     : 1713
% 8.02/2.70  #Fact    : 0
% 8.02/2.70  #Define  : 0
% 8.02/2.70  #Split   : 36
% 8.02/2.70  #Chain   : 0
% 8.02/2.70  #Close   : 0
% 8.02/2.70  
% 8.02/2.70  Ordering : KBO
% 8.02/2.70  
% 8.02/2.70  Simplification rules
% 8.02/2.70  ----------------------
% 8.02/2.70  #Subsume      : 200
% 8.02/2.70  #Demod        : 1216
% 8.02/2.70  #Tautology    : 754
% 8.02/2.70  #SimpNegUnit  : 9
% 8.02/2.70  #BackRed      : 217
% 8.02/2.70  
% 8.02/2.70  #Partial instantiations: 0
% 8.02/2.70  #Strategies tried      : 1
% 8.02/2.70  
% 8.02/2.70  Timing (in seconds)
% 8.02/2.70  ----------------------
% 8.02/2.71  Preprocessing        : 0.40
% 8.02/2.71  Parsing              : 0.20
% 8.02/2.71  CNF conversion       : 0.04
% 8.02/2.71  Main loop            : 1.46
% 8.02/2.71  Inferencing          : 0.51
% 8.02/2.71  Reduction            : 0.51
% 8.02/2.71  Demodulation         : 0.36
% 8.02/2.71  BG Simplification    : 0.06
% 8.02/2.71  Subsumption          : 0.25
% 8.02/2.71  Abstraction          : 0.06
% 8.02/2.71  MUC search           : 0.00
% 8.02/2.71  Cooper               : 0.00
% 8.02/2.71  Total                : 1.96
% 8.02/2.71  Index Insertion      : 0.00
% 8.02/2.71  Index Deletion       : 0.00
% 8.02/2.71  Index Matching       : 0.00
% 8.02/2.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
