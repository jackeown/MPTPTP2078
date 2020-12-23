%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:37 EST 2020

% Result     : Theorem 8.96s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  263 (1263 expanded)
%              Number of leaves         :   48 ( 413 expanded)
%              Depth                    :   13
%              Number of atoms          :  438 (3562 expanded)
%              Number of equality atoms :  135 ( 515 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_101,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_97,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_127,axiom,(
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

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_141,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_135,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_33,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_43,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_82,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_76,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_146,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_159,plain,(
    v1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_146])).

tff(c_14,plain,(
    ! [B_7] : r1_tarski(B_7,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8207,plain,(
    ! [A_722,B_723,C_724,D_725] :
      ( k7_relset_1(A_722,B_723,C_724,D_725) = k9_relat_1(C_724,D_725)
      | ~ m1_subset_1(C_724,k1_zfmisc_1(k2_zfmisc_1(A_722,B_723))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_8219,plain,(
    ! [D_726] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_726) = k9_relat_1('#skF_6',D_726) ),
    inference(resolution,[status(thm)],[c_76,c_8207])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1393,plain,(
    ! [C_208,B_209,A_210] :
      ( ~ v1_xboole_0(C_208)
      | ~ m1_subset_1(B_209,k1_zfmisc_1(C_208))
      | ~ r2_hidden(A_210,B_209) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1420,plain,(
    ! [B_213,A_214,A_215] :
      ( ~ v1_xboole_0(B_213)
      | ~ r2_hidden(A_214,A_215)
      | ~ r1_tarski(A_215,B_213) ) ),
    inference(resolution,[status(thm)],[c_26,c_1393])).

tff(c_4059,plain,(
    ! [B_397,A_398,B_399] :
      ( ~ v1_xboole_0(B_397)
      | ~ r1_tarski(A_398,B_397)
      | r1_tarski(A_398,B_399) ) ),
    inference(resolution,[status(thm)],[c_6,c_1420])).

tff(c_4076,plain,(
    ! [B_400,B_401] :
      ( ~ v1_xboole_0(B_400)
      | r1_tarski(B_400,B_401) ) ),
    inference(resolution,[status(thm)],[c_14,c_4059])).

tff(c_72,plain,(
    r1_tarski(k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_129,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_139,plain,
    ( k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4'
    | ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_72,c_129])).

tff(c_1378,plain,(
    ~ r1_tarski('#skF_4',k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_139])).

tff(c_4100,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_4076,c_1378])).

tff(c_74,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_78,plain,(
    v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_4903,plain,(
    ! [A_480,B_481,C_482] :
      ( k1_relset_1(A_480,B_481,C_482) = k1_relat_1(C_482)
      | ~ m1_subset_1(C_482,k1_zfmisc_1(k2_zfmisc_1(A_480,B_481))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4922,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_4903])).

tff(c_6515,plain,(
    ! [B_591,A_592,C_593] :
      ( k1_xboole_0 = B_591
      | k1_relset_1(A_592,B_591,C_593) = A_592
      | ~ v1_funct_2(C_593,A_592,B_591)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(A_592,B_591))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6534,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_6515])).

tff(c_6548,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4922,c_6534])).

tff(c_6550,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6548])).

tff(c_36,plain,(
    ! [B_21,A_20] :
      ( k1_relat_1(k7_relat_1(B_21,A_20)) = A_20
      | ~ r1_tarski(A_20,k1_relat_1(B_21))
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6567,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6550,c_36])).

tff(c_7021,plain,(
    ! [A_614] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_614)) = A_614
      | ~ r1_tarski(A_614,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_6567])).

tff(c_80,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_5886,plain,(
    ! [A_551,B_552,C_553,D_554] :
      ( k2_partfun1(A_551,B_552,C_553,D_554) = k7_relat_1(C_553,D_554)
      | ~ m1_subset_1(C_553,k1_zfmisc_1(k2_zfmisc_1(A_551,B_552)))
      | ~ v1_funct_1(C_553) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_5895,plain,(
    ! [D_554] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_554) = k7_relat_1('#skF_6',D_554)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_5886])).

tff(c_5906,plain,(
    ! [D_554] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_554) = k7_relat_1('#skF_6',D_554) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5895])).

tff(c_1941,plain,(
    ! [A_281,B_282,C_283] :
      ( k1_relset_1(A_281,B_282,C_283) = k1_relat_1(C_283)
      | ~ m1_subset_1(C_283,k1_zfmisc_1(k2_zfmisc_1(A_281,B_282))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1956,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_1941])).

tff(c_3680,plain,(
    ! [B_385,A_386,C_387] :
      ( k1_xboole_0 = B_385
      | k1_relset_1(A_386,B_385,C_387) = A_386
      | ~ v1_funct_2(C_387,A_386,B_385)
      | ~ m1_subset_1(C_387,k1_zfmisc_1(k2_zfmisc_1(A_386,B_385))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_3693,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_3680])).

tff(c_3704,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1956,c_3693])).

tff(c_3706,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3704])).

tff(c_3719,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3706,c_36])).

tff(c_3906,plain,(
    ! [A_393] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_393)) = A_393
      | ~ r1_tarski(A_393,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_3719])).

tff(c_2152,plain,(
    ! [A_294,B_295,C_296,D_297] :
      ( k7_relset_1(A_294,B_295,C_296,D_297) = k9_relat_1(C_296,D_297)
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2163,plain,(
    ! [D_297] : k7_relset_1('#skF_2','#skF_5','#skF_6',D_297) = k9_relat_1('#skF_6',D_297) ),
    inference(resolution,[status(thm)],[c_76,c_2152])).

tff(c_2224,plain,(
    r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2163,c_72])).

tff(c_34,plain,(
    ! [B_19,A_18] :
      ( k2_relat_1(k7_relat_1(B_19,A_18)) = k9_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2637,plain,(
    ! [A_331,B_332,C_333,D_334] :
      ( k2_partfun1(A_331,B_332,C_333,D_334) = k7_relat_1(C_333,D_334)
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_331,B_332)))
      | ~ v1_funct_1(C_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_2644,plain,(
    ! [D_334] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_334) = k7_relat_1('#skF_6',D_334)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_2637])).

tff(c_2652,plain,(
    ! [D_334] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_334) = k7_relat_1('#skF_6',D_334) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2644])).

tff(c_3514,plain,(
    ! [A_380,B_381,C_382,D_383] :
      ( m1_subset_1(k2_partfun1(A_380,B_381,C_382,D_383),k1_zfmisc_1(k2_zfmisc_1(A_380,B_381)))
      | ~ m1_subset_1(C_382,k1_zfmisc_1(k2_zfmisc_1(A_380,B_381)))
      | ~ v1_funct_1(C_382) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_3549,plain,(
    ! [D_334] :
      ( m1_subset_1(k7_relat_1('#skF_6',D_334),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2652,c_3514])).

tff(c_3575,plain,(
    ! [D_384] : m1_subset_1(k7_relat_1('#skF_6',D_384),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_3549])).

tff(c_38,plain,(
    ! [C_24,A_22,B_23] :
      ( v1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_3622,plain,(
    ! [D_384] : v1_relat_1(k7_relat_1('#skF_6',D_384)) ),
    inference(resolution,[status(thm)],[c_3575,c_38])).

tff(c_2727,plain,(
    ! [C_343,A_344,B_345] :
      ( m1_subset_1(C_343,k1_zfmisc_1(k2_zfmisc_1(A_344,B_345)))
      | ~ r1_tarski(k2_relat_1(C_343),B_345)
      | ~ r1_tarski(k1_relat_1(C_343),A_344)
      | ~ v1_relat_1(C_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_1319,plain,(
    ! [A_193,B_194,C_195,D_196] :
      ( v1_funct_1(k2_partfun1(A_193,B_194,C_195,D_196))
      | ~ m1_subset_1(C_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(C_195) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_1326,plain,(
    ! [D_196] :
      ( v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_196))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_1319])).

tff(c_1334,plain,(
    ! [D_196] : v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6',D_196)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_1326])).

tff(c_70,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4')))
    | ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_160,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_1337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1334,c_160])).

tff(c_1338,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_1425,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1338])).

tff(c_2678,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2652,c_1425])).

tff(c_2766,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2727,c_2678])).

tff(c_2820,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_2766])).

tff(c_3627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3622,c_2820])).

tff(c_3628,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_2766])).

tff(c_3630,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3628])).

tff(c_3633,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_3630])).

tff(c_3639,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_2224,c_3633])).

tff(c_3640,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_3628])).

tff(c_3918,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3906,c_3640])).

tff(c_3979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14,c_3918])).

tff(c_3980,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3704])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4054,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3980,c_8])).

tff(c_4056,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_4054])).

tff(c_4057,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_5917,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5906,c_4057])).

tff(c_4058,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_4920,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4058,c_4903])).

tff(c_5911,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = k1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5906,c_5906,c_4920])).

tff(c_5916,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5906,c_4058])).

tff(c_6242,plain,(
    ! [B_570,C_571,A_572] :
      ( k1_xboole_0 = B_570
      | v1_funct_2(C_571,A_572,B_570)
      | k1_relset_1(A_572,B_570,C_571) != A_572
      | ~ m1_subset_1(C_571,k1_zfmisc_1(k2_zfmisc_1(A_572,B_570))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_6251,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_5916,c_6242])).

tff(c_6270,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5911,c_6251])).

tff(c_6271,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5917,c_6270])).

tff(c_6276,plain,(
    k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6271])).

tff(c_7030,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_7021,c_6276])).

tff(c_7099,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_7030])).

tff(c_7100,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_6548])).

tff(c_7153,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7100,c_8])).

tff(c_7155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_7153])).

tff(c_7156,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6271])).

tff(c_7210,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7156,c_8])).

tff(c_7212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4100,c_7210])).

tff(c_7213,plain,(
    k7_relset_1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_139])).

tff(c_8225,plain,(
    k9_relat_1('#skF_6','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_8219,c_7213])).

tff(c_7721,plain,(
    ! [A_688,B_689,C_690] :
      ( k1_relset_1(A_688,B_689,C_690) = k1_relat_1(C_690)
      | ~ m1_subset_1(C_690,k1_zfmisc_1(k2_zfmisc_1(A_688,B_689))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_7736,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_7721])).

tff(c_9210,plain,(
    ! [B_793,A_794,C_795] :
      ( k1_xboole_0 = B_793
      | k1_relset_1(A_794,B_793,C_795) = A_794
      | ~ v1_funct_2(C_795,A_794,B_793)
      | ~ m1_subset_1(C_795,k1_zfmisc_1(k2_zfmisc_1(A_794,B_793))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_9223,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_9210])).

tff(c_9234,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_7736,c_9223])).

tff(c_9236,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9234])).

tff(c_9249,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9236,c_36])).

tff(c_9272,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_9249])).

tff(c_8485,plain,(
    ! [A_741,B_742,C_743,D_744] :
      ( k2_partfun1(A_741,B_742,C_743,D_744) = k7_relat_1(C_743,D_744)
      | ~ m1_subset_1(C_743,k1_zfmisc_1(k2_zfmisc_1(A_741,B_742)))
      | ~ v1_funct_1(C_743) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_8494,plain,(
    ! [D_744] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_744) = k7_relat_1('#skF_6',D_744)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_8485])).

tff(c_8503,plain,(
    ! [D_744] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_744) = k7_relat_1('#skF_6',D_744) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_8494])).

tff(c_9355,plain,(
    ! [A_797,B_798,C_799,D_800] :
      ( m1_subset_1(k2_partfun1(A_797,B_798,C_799,D_800),k1_zfmisc_1(k2_zfmisc_1(A_797,B_798)))
      | ~ m1_subset_1(C_799,k1_zfmisc_1(k2_zfmisc_1(A_797,B_798)))
      | ~ v1_funct_1(C_799) ) ),
    inference(cnfTransformation,[status(thm)],[f_135])).

tff(c_9390,plain,(
    ! [D_744] :
      ( m1_subset_1(k7_relat_1('#skF_6',D_744),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5')))
      | ~ v1_funct_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8503,c_9355])).

tff(c_9551,plain,(
    ! [D_808] : m1_subset_1(k7_relat_1('#skF_6',D_808),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_76,c_9390])).

tff(c_9598,plain,(
    ! [D_808] : v1_relat_1(k7_relat_1('#skF_6',D_808)) ),
    inference(resolution,[status(thm)],[c_9551,c_38])).

tff(c_50,plain,(
    ! [C_41,A_39,B_40] :
      ( m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | ~ r1_tarski(k2_relat_1(C_41),B_40)
      | ~ r1_tarski(k1_relat_1(C_41),A_39)
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7236,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitLeft,[status(thm)],[c_1338])).

tff(c_8507,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8503,c_7236])).

tff(c_8524,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_50,c_8507])).

tff(c_9799,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9598,c_8524])).

tff(c_9800,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9799])).

tff(c_9967,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_9272,c_9800])).

tff(c_9979,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_14,c_9967])).

tff(c_9980,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_6','#skF_3')),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_9799])).

tff(c_10126,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_6','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_9980])).

tff(c_10130,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_14,c_8225,c_10126])).

tff(c_10131,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_9234])).

tff(c_10181,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10131,c_8])).

tff(c_10183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_10181])).

tff(c_10185,plain,(
    m1_subset_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_10510,plain,(
    ! [C_890,B_891,A_892] :
      ( v1_xboole_0(C_890)
      | ~ m1_subset_1(C_890,k1_zfmisc_1(k2_zfmisc_1(B_891,A_892)))
      | ~ v1_xboole_0(A_892) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_10527,plain,
    ( v1_xboole_0(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'))
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_10185,c_10510])).

tff(c_10569,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_10527])).

tff(c_10881,plain,(
    ! [A_910,B_911,C_912] :
      ( k1_relset_1(A_910,B_911,C_912) = k1_relat_1(C_912)
      | ~ m1_subset_1(C_912,k1_zfmisc_1(k2_zfmisc_1(A_910,B_911))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_10900,plain,(
    k1_relset_1('#skF_2','#skF_5','#skF_6') = k1_relat_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_76,c_10881])).

tff(c_12421,plain,(
    ! [B_1014,A_1015,C_1016] :
      ( k1_xboole_0 = B_1014
      | k1_relset_1(A_1015,B_1014,C_1016) = A_1015
      | ~ v1_funct_2(C_1016,A_1015,B_1014)
      | ~ m1_subset_1(C_1016,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1014))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12440,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relset_1('#skF_2','#skF_5','#skF_6') = '#skF_2'
    | ~ v1_funct_2('#skF_6','#skF_2','#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_12421])).

tff(c_12454,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_relat_1('#skF_6') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_10900,c_12440])).

tff(c_12456,plain,(
    k1_relat_1('#skF_6') = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12454])).

tff(c_12476,plain,(
    ! [A_20] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_20)) = A_20
      | ~ r1_tarski(A_20,'#skF_2')
      | ~ v1_relat_1('#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12456,c_36])).

tff(c_12981,plain,(
    ! [A_1039] :
      ( k1_relat_1(k7_relat_1('#skF_6',A_1039)) = A_1039
      | ~ r1_tarski(A_1039,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_12476])).

tff(c_11852,plain,(
    ! [A_982,B_983,C_984,D_985] :
      ( k2_partfun1(A_982,B_983,C_984,D_985) = k7_relat_1(C_984,D_985)
      | ~ m1_subset_1(C_984,k1_zfmisc_1(k2_zfmisc_1(A_982,B_983)))
      | ~ v1_funct_1(C_984) ) ),
    inference(cnfTransformation,[status(thm)],[f_141])).

tff(c_11861,plain,(
    ! [D_985] :
      ( k2_partfun1('#skF_2','#skF_5','#skF_6',D_985) = k7_relat_1('#skF_6',D_985)
      | ~ v1_funct_1('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_76,c_11852])).

tff(c_11872,plain,(
    ! [D_985] : k2_partfun1('#skF_2','#skF_5','#skF_6',D_985) = k7_relat_1('#skF_6',D_985) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_11861])).

tff(c_10898,plain,(
    k1_relset_1('#skF_3','#skF_4',k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) = k1_relat_1(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10185,c_10881])).

tff(c_12036,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) = k1_relat_1(k7_relat_1('#skF_6','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11872,c_11872,c_10898])).

tff(c_10184,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_12042,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11872,c_10184])).

tff(c_12041,plain,(
    m1_subset_1(k7_relat_1('#skF_6','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11872,c_10185])).

tff(c_12196,plain,(
    ! [B_1001,C_1002,A_1003] :
      ( k1_xboole_0 = B_1001
      | v1_funct_2(C_1002,A_1003,B_1001)
      | k1_relset_1(A_1003,B_1001,C_1002) != A_1003
      | ~ m1_subset_1(C_1002,k1_zfmisc_1(k2_zfmisc_1(A_1003,B_1001))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_12199,plain,
    ( k1_xboole_0 = '#skF_4'
    | v1_funct_2(k7_relat_1('#skF_6','#skF_3'),'#skF_3','#skF_4')
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_12041,c_12196])).

tff(c_12221,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_12042,c_12199])).

tff(c_12227,plain,(
    k1_relset_1('#skF_3','#skF_4',k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_12221])).

tff(c_12238,plain,(
    k1_relat_1(k7_relat_1('#skF_6','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12036,c_12227])).

tff(c_12993,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12981,c_12238])).

tff(c_13061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_12993])).

tff(c_13062,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_12454])).

tff(c_13116,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13062,c_8])).

tff(c_13118,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_82,c_13116])).

tff(c_13119,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12221])).

tff(c_13170,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13119,c_8])).

tff(c_13172,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10569,c_13170])).

tff(c_13174,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_10527])).

tff(c_10187,plain,(
    ! [C_830,B_831,A_832] :
      ( ~ v1_xboole_0(C_830)
      | ~ m1_subset_1(B_831,k1_zfmisc_1(C_830))
      | ~ r2_hidden(A_832,B_831) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10195,plain,(
    ! [B_833,A_834,A_835] :
      ( ~ v1_xboole_0(B_833)
      | ~ r2_hidden(A_834,A_835)
      | ~ r1_tarski(A_835,B_833) ) ),
    inference(resolution,[status(thm)],[c_26,c_10187])).

tff(c_10219,plain,(
    ! [B_839,A_840,B_841] :
      ( ~ v1_xboole_0(B_839)
      | ~ r1_tarski(A_840,B_839)
      | r1_tarski(A_840,B_841) ) ),
    inference(resolution,[status(thm)],[c_6,c_10195])).

tff(c_10233,plain,(
    ! [B_842,B_843] :
      ( ~ v1_xboole_0(B_842)
      | r1_tarski(B_842,B_843) ) ),
    inference(resolution,[status(thm)],[c_14,c_10219])).

tff(c_16,plain,(
    ! [A_8] :
      ( k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10262,plain,(
    ! [B_842] :
      ( k1_xboole_0 = B_842
      | ~ v1_xboole_0(B_842) ) ),
    inference(resolution,[status(thm)],[c_10233,c_16])).

tff(c_13258,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13174,c_10262])).

tff(c_1363,plain,(
    ! [A_201,A_202,B_203] :
      ( v1_relat_1(A_201)
      | ~ r1_tarski(A_201,k2_zfmisc_1(A_202,B_203)) ) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_1377,plain,(
    ! [A_202,B_203] : v1_relat_1(k2_zfmisc_1(A_202,B_203)) ),
    inference(resolution,[status(thm)],[c_14,c_1363])).

tff(c_22,plain,(
    ! [B_10] : k2_zfmisc_1(k1_xboole_0,B_10) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10354,plain,(
    ! [C_862,A_863,B_864] :
      ( v4_relat_1(C_862,A_863)
      | ~ m1_subset_1(C_862,k1_zfmisc_1(k2_zfmisc_1(A_863,B_864))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_10464,plain,(
    ! [A_885,A_886,B_887] :
      ( v4_relat_1(A_885,A_886)
      | ~ r1_tarski(A_885,k2_zfmisc_1(A_886,B_887)) ) ),
    inference(resolution,[status(thm)],[c_26,c_10354])).

tff(c_10496,plain,(
    ! [A_888,B_889] : v4_relat_1(k2_zfmisc_1(A_888,B_889),A_888) ),
    inference(resolution,[status(thm)],[c_14,c_10464])).

tff(c_10199,plain,(
    ! [B_836,A_837] :
      ( r1_tarski(k1_relat_1(B_836),A_837)
      | ~ v4_relat_1(B_836,A_837)
      | ~ v1_relat_1(B_836) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10217,plain,(
    ! [B_836] :
      ( k1_relat_1(B_836) = k1_xboole_0
      | ~ v4_relat_1(B_836,k1_xboole_0)
      | ~ v1_relat_1(B_836) ) ),
    inference(resolution,[status(thm)],[c_10199,c_16])).

tff(c_10500,plain,(
    ! [B_889] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_889)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_889)) ) ),
    inference(resolution,[status(thm)],[c_10496,c_10217])).

tff(c_10509,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_22,c_10500])).

tff(c_13261,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_13258,c_10509])).

tff(c_158,plain,(
    ! [A_11,A_67,B_68] :
      ( v1_relat_1(A_11)
      | ~ r1_tarski(A_11,k2_zfmisc_1(A_67,B_68)) ) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_10258,plain,(
    ! [B_842] :
      ( v1_relat_1(B_842)
      | ~ v1_xboole_0(B_842) ) ),
    inference(resolution,[status(thm)],[c_10233,c_158])).

tff(c_13259,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13174,c_10258])).

tff(c_20,plain,(
    ! [A_9] : k2_zfmisc_1(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10506,plain,(
    ! [A_9] : v4_relat_1(k1_xboole_0,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_10496])).

tff(c_13260,plain,(
    ! [A_9] : v4_relat_1('#skF_4',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_10506])).

tff(c_32,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v4_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_13396,plain,(
    ! [A_16] :
      ( r1_tarski('#skF_4',A_16)
      | ~ v4_relat_1('#skF_4',A_16)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13261,c_32])).

tff(c_13406,plain,(
    ! [A_16] : r1_tarski('#skF_4',A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13259,c_13260,c_13396])).

tff(c_13788,plain,(
    ! [A_1070,B_1071,C_1072] :
      ( k1_relset_1(A_1070,B_1071,C_1072) = k1_relat_1(C_1072)
      | ~ m1_subset_1(C_1072,k1_zfmisc_1(k2_zfmisc_1(A_1070,B_1071))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_15078,plain,(
    ! [A_1147,B_1148,A_1149] :
      ( k1_relset_1(A_1147,B_1148,A_1149) = k1_relat_1(A_1149)
      | ~ r1_tarski(A_1149,k2_zfmisc_1(A_1147,B_1148)) ) ),
    inference(resolution,[status(thm)],[c_26,c_13788])).

tff(c_15091,plain,(
    ! [A_1147,B_1148] : k1_relset_1(A_1147,B_1148,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_13406,c_15078])).

tff(c_15108,plain,(
    ! [A_1147,B_1148] : k1_relset_1(A_1147,B_1148,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13261,c_15091])).

tff(c_13185,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13174,c_10262])).

tff(c_52,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_42,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_85,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_52])).

tff(c_13175,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_85])).

tff(c_13239,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13185,c_13185,c_13175])).

tff(c_13242,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_13239])).

tff(c_13246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_13242])).

tff(c_13248,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_13372,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_13258,c_13248])).

tff(c_56,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_84,plain,(
    ! [C_44,B_43] :
      ( v1_funct_2(C_44,k1_xboole_0,B_43)
      | k1_relset_1(k1_xboole_0,B_43,C_44) != k1_xboole_0
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_56])).

tff(c_13855,plain,(
    ! [C_1079,B_1080] :
      ( v1_funct_2(C_1079,'#skF_4',B_1080)
      | k1_relset_1('#skF_4',B_1080,C_1079) != '#skF_4'
      | ~ m1_subset_1(C_1079,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_13258,c_13258,c_13258,c_84])).

tff(c_14705,plain,(
    ! [B_1135] :
      ( v1_funct_2('#skF_4','#skF_4',B_1135)
      | k1_relset_1('#skF_4',B_1135,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_13372,c_13855])).

tff(c_13247,plain,(
    ! [A_42] :
      ( v1_funct_2(k1_xboole_0,A_42,k1_xboole_0)
      | k1_xboole_0 = A_42 ) ),
    inference(splitRight,[status(thm)],[c_85])).

tff(c_13542,plain,(
    ! [A_42] :
      ( v1_funct_2('#skF_4',A_42,'#skF_4')
      | A_42 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_13258,c_13258,c_13247])).

tff(c_13173,plain,(
    v1_xboole_0(k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_10527])).

tff(c_13268,plain,(
    ! [B_842] :
      ( B_842 = '#skF_4'
      | ~ v1_xboole_0(B_842) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13258,c_10262])).

tff(c_13640,plain,(
    k2_partfun1('#skF_2','#skF_5','#skF_6','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13173,c_13268])).

tff(c_13758,plain,(
    ~ v1_funct_2('#skF_4','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13640,c_10184])).

tff(c_13773,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_13542,c_13758])).

tff(c_13774,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13773,c_13758])).

tff(c_14717,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_14705,c_13774])).

tff(c_15118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_15108,c_14717])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:15:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.96/3.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.17  
% 8.96/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.96/3.18  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 8.96/3.18  
% 8.96/3.18  %Foreground sorts:
% 8.96/3.18  
% 8.96/3.18  
% 8.96/3.18  %Background operators:
% 8.96/3.18  
% 8.96/3.18  
% 8.96/3.18  %Foreground operators:
% 8.96/3.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.96/3.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.96/3.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.96/3.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.96/3.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.96/3.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.96/3.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.96/3.18  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 8.96/3.18  tff('#skF_5', type, '#skF_5': $i).
% 8.96/3.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.96/3.18  tff('#skF_6', type, '#skF_6': $i).
% 8.96/3.18  tff('#skF_2', type, '#skF_2': $i).
% 8.96/3.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 8.96/3.18  tff('#skF_3', type, '#skF_3': $i).
% 8.96/3.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.96/3.18  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.96/3.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.96/3.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.96/3.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.96/3.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.96/3.18  tff('#skF_4', type, '#skF_4': $i).
% 8.96/3.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.96/3.18  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.96/3.18  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.96/3.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 8.96/3.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.96/3.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.96/3.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.96/3.18  
% 9.14/3.21  tff(f_162, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t178_funct_2)).
% 9.14/3.21  tff(f_80, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 9.14/3.21  tff(f_39, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.14/3.21  tff(f_101, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.14/3.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.14/3.21  tff(f_53, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.14/3.21  tff(f_60, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 9.14/3.21  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.14/3.21  tff(f_127, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 9.14/3.21  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 9.14/3.21  tff(f_141, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.14/3.21  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 9.14/3.21  tff(f_135, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.14/3.21  tff(f_109, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 9.14/3.21  tff(f_33, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.14/3.21  tff(f_93, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 9.14/3.21  tff(f_43, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 9.14/3.21  tff(f_49, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.14/3.21  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.14/3.21  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 9.14/3.21  tff(c_82, plain, (~v1_xboole_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_76, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_146, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.14/3.21  tff(c_159, plain, (v1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_146])).
% 9.14/3.21  tff(c_14, plain, (![B_7]: (r1_tarski(B_7, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.14/3.21  tff(c_8207, plain, (![A_722, B_723, C_724, D_725]: (k7_relset_1(A_722, B_723, C_724, D_725)=k9_relat_1(C_724, D_725) | ~m1_subset_1(C_724, k1_zfmisc_1(k2_zfmisc_1(A_722, B_723))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.14/3.21  tff(c_8219, plain, (![D_726]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_726)=k9_relat_1('#skF_6', D_726))), inference(resolution, [status(thm)], [c_76, c_8207])).
% 9.14/3.21  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.14/3.21  tff(c_26, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.14/3.21  tff(c_1393, plain, (![C_208, B_209, A_210]: (~v1_xboole_0(C_208) | ~m1_subset_1(B_209, k1_zfmisc_1(C_208)) | ~r2_hidden(A_210, B_209))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.14/3.21  tff(c_1420, plain, (![B_213, A_214, A_215]: (~v1_xboole_0(B_213) | ~r2_hidden(A_214, A_215) | ~r1_tarski(A_215, B_213))), inference(resolution, [status(thm)], [c_26, c_1393])).
% 9.14/3.21  tff(c_4059, plain, (![B_397, A_398, B_399]: (~v1_xboole_0(B_397) | ~r1_tarski(A_398, B_397) | r1_tarski(A_398, B_399))), inference(resolution, [status(thm)], [c_6, c_1420])).
% 9.14/3.21  tff(c_4076, plain, (![B_400, B_401]: (~v1_xboole_0(B_400) | r1_tarski(B_400, B_401))), inference(resolution, [status(thm)], [c_14, c_4059])).
% 9.14/3.21  tff(c_72, plain, (r1_tarski(k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_129, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.14/3.21  tff(c_139, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4' | ~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_72, c_129])).
% 9.14/3.21  tff(c_1378, plain, (~r1_tarski('#skF_4', k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_139])).
% 9.14/3.21  tff(c_4100, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_4076, c_1378])).
% 9.14/3.21  tff(c_74, plain, (r1_tarski('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_78, plain, (v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_4903, plain, (![A_480, B_481, C_482]: (k1_relset_1(A_480, B_481, C_482)=k1_relat_1(C_482) | ~m1_subset_1(C_482, k1_zfmisc_1(k2_zfmisc_1(A_480, B_481))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.21  tff(c_4922, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_4903])).
% 9.14/3.21  tff(c_6515, plain, (![B_591, A_592, C_593]: (k1_xboole_0=B_591 | k1_relset_1(A_592, B_591, C_593)=A_592 | ~v1_funct_2(C_593, A_592, B_591) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(A_592, B_591))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_6534, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_6515])).
% 9.14/3.21  tff(c_6548, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_4922, c_6534])).
% 9.14/3.21  tff(c_6550, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_6548])).
% 9.14/3.21  tff(c_36, plain, (![B_21, A_20]: (k1_relat_1(k7_relat_1(B_21, A_20))=A_20 | ~r1_tarski(A_20, k1_relat_1(B_21)) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_76])).
% 9.14/3.21  tff(c_6567, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_6', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6550, c_36])).
% 9.14/3.21  tff(c_7021, plain, (![A_614]: (k1_relat_1(k7_relat_1('#skF_6', A_614))=A_614 | ~r1_tarski(A_614, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_6567])).
% 9.14/3.21  tff(c_80, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_5886, plain, (![A_551, B_552, C_553, D_554]: (k2_partfun1(A_551, B_552, C_553, D_554)=k7_relat_1(C_553, D_554) | ~m1_subset_1(C_553, k1_zfmisc_1(k2_zfmisc_1(A_551, B_552))) | ~v1_funct_1(C_553))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.14/3.21  tff(c_5895, plain, (![D_554]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_554)=k7_relat_1('#skF_6', D_554) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_5886])).
% 9.14/3.21  tff(c_5906, plain, (![D_554]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_554)=k7_relat_1('#skF_6', D_554))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5895])).
% 9.14/3.21  tff(c_1941, plain, (![A_281, B_282, C_283]: (k1_relset_1(A_281, B_282, C_283)=k1_relat_1(C_283) | ~m1_subset_1(C_283, k1_zfmisc_1(k2_zfmisc_1(A_281, B_282))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.21  tff(c_1956, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_1941])).
% 9.14/3.21  tff(c_3680, plain, (![B_385, A_386, C_387]: (k1_xboole_0=B_385 | k1_relset_1(A_386, B_385, C_387)=A_386 | ~v1_funct_2(C_387, A_386, B_385) | ~m1_subset_1(C_387, k1_zfmisc_1(k2_zfmisc_1(A_386, B_385))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_3693, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_3680])).
% 9.14/3.21  tff(c_3704, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_1956, c_3693])).
% 9.14/3.21  tff(c_3706, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_3704])).
% 9.14/3.21  tff(c_3719, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_6', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_3706, c_36])).
% 9.14/3.21  tff(c_3906, plain, (![A_393]: (k1_relat_1(k7_relat_1('#skF_6', A_393))=A_393 | ~r1_tarski(A_393, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_3719])).
% 9.14/3.21  tff(c_2152, plain, (![A_294, B_295, C_296, D_297]: (k7_relset_1(A_294, B_295, C_296, D_297)=k9_relat_1(C_296, D_297) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.14/3.21  tff(c_2163, plain, (![D_297]: (k7_relset_1('#skF_2', '#skF_5', '#skF_6', D_297)=k9_relat_1('#skF_6', D_297))), inference(resolution, [status(thm)], [c_76, c_2152])).
% 9.14/3.21  tff(c_2224, plain, (r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2163, c_72])).
% 9.14/3.21  tff(c_34, plain, (![B_19, A_18]: (k2_relat_1(k7_relat_1(B_19, A_18))=k9_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.14/3.21  tff(c_2637, plain, (![A_331, B_332, C_333, D_334]: (k2_partfun1(A_331, B_332, C_333, D_334)=k7_relat_1(C_333, D_334) | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_331, B_332))) | ~v1_funct_1(C_333))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.14/3.21  tff(c_2644, plain, (![D_334]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_334)=k7_relat_1('#skF_6', D_334) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_2637])).
% 9.14/3.21  tff(c_2652, plain, (![D_334]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_334)=k7_relat_1('#skF_6', D_334))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2644])).
% 9.14/3.21  tff(c_3514, plain, (![A_380, B_381, C_382, D_383]: (m1_subset_1(k2_partfun1(A_380, B_381, C_382, D_383), k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))) | ~m1_subset_1(C_382, k1_zfmisc_1(k2_zfmisc_1(A_380, B_381))) | ~v1_funct_1(C_382))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.14/3.21  tff(c_3549, plain, (![D_334]: (m1_subset_1(k7_relat_1('#skF_6', D_334), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2652, c_3514])).
% 9.14/3.21  tff(c_3575, plain, (![D_384]: (m1_subset_1(k7_relat_1('#skF_6', D_384), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_3549])).
% 9.14/3.21  tff(c_38, plain, (![C_24, A_22, B_23]: (v1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_80])).
% 9.14/3.21  tff(c_3622, plain, (![D_384]: (v1_relat_1(k7_relat_1('#skF_6', D_384)))), inference(resolution, [status(thm)], [c_3575, c_38])).
% 9.14/3.21  tff(c_2727, plain, (![C_343, A_344, B_345]: (m1_subset_1(C_343, k1_zfmisc_1(k2_zfmisc_1(A_344, B_345))) | ~r1_tarski(k2_relat_1(C_343), B_345) | ~r1_tarski(k1_relat_1(C_343), A_344) | ~v1_relat_1(C_343))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.14/3.21  tff(c_1319, plain, (![A_193, B_194, C_195, D_196]: (v1_funct_1(k2_partfun1(A_193, B_194, C_195, D_196)) | ~m1_subset_1(C_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(C_195))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.14/3.21  tff(c_1326, plain, (![D_196]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_196)) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_1319])).
% 9.14/3.21  tff(c_1334, plain, (![D_196]: (v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_196)))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_1326])).
% 9.14/3.21  tff(c_70, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4'))) | ~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 9.14/3.21  tff(c_160, plain, (~v1_funct_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_70])).
% 9.14/3.21  tff(c_1337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1334, c_160])).
% 9.14/3.21  tff(c_1338, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_70])).
% 9.14/3.21  tff(c_1425, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_2678, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2652, c_1425])).
% 9.14/3.21  tff(c_2766, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_2727, c_2678])).
% 9.14/3.21  tff(c_2820, plain, (~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(splitLeft, [status(thm)], [c_2766])).
% 9.14/3.21  tff(c_3627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3622, c_2820])).
% 9.14/3.21  tff(c_3628, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_2766])).
% 9.14/3.21  tff(c_3630, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitLeft, [status(thm)], [c_3628])).
% 9.14/3.21  tff(c_3633, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34, c_3630])).
% 9.14/3.21  tff(c_3639, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_2224, c_3633])).
% 9.14/3.21  tff(c_3640, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_3628])).
% 9.14/3.21  tff(c_3918, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3906, c_3640])).
% 9.14/3.21  tff(c_3979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_14, c_3918])).
% 9.14/3.21  tff(c_3980, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3704])).
% 9.14/3.21  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.14/3.21  tff(c_4054, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3980, c_8])).
% 9.14/3.21  tff(c_4056, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_4054])).
% 9.14/3.21  tff(c_4057, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_5917, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5906, c_4057])).
% 9.14/3.21  tff(c_4058, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_4920, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_4058, c_4903])).
% 9.14/3.21  tff(c_5911, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_5906, c_5906, c_4920])).
% 9.14/3.21  tff(c_5916, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5906, c_4058])).
% 9.14/3.21  tff(c_6242, plain, (![B_570, C_571, A_572]: (k1_xboole_0=B_570 | v1_funct_2(C_571, A_572, B_570) | k1_relset_1(A_572, B_570, C_571)!=A_572 | ~m1_subset_1(C_571, k1_zfmisc_1(k2_zfmisc_1(A_572, B_570))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_6251, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_5916, c_6242])).
% 9.14/3.21  tff(c_6270, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_5911, c_6251])).
% 9.14/3.21  tff(c_6271, plain, (k1_xboole_0='#skF_4' | k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5917, c_6270])).
% 9.14/3.21  tff(c_6276, plain, (k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_6271])).
% 9.14/3.21  tff(c_7030, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_7021, c_6276])).
% 9.14/3.21  tff(c_7099, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_7030])).
% 9.14/3.21  tff(c_7100, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_6548])).
% 9.14/3.21  tff(c_7153, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7100, c_8])).
% 9.14/3.21  tff(c_7155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_7153])).
% 9.14/3.21  tff(c_7156, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_6271])).
% 9.14/3.21  tff(c_7210, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7156, c_8])).
% 9.14/3.21  tff(c_7212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4100, c_7210])).
% 9.14/3.21  tff(c_7213, plain, (k7_relset_1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_139])).
% 9.14/3.21  tff(c_8225, plain, (k9_relat_1('#skF_6', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_8219, c_7213])).
% 9.14/3.21  tff(c_7721, plain, (![A_688, B_689, C_690]: (k1_relset_1(A_688, B_689, C_690)=k1_relat_1(C_690) | ~m1_subset_1(C_690, k1_zfmisc_1(k2_zfmisc_1(A_688, B_689))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.21  tff(c_7736, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_7721])).
% 9.14/3.21  tff(c_9210, plain, (![B_793, A_794, C_795]: (k1_xboole_0=B_793 | k1_relset_1(A_794, B_793, C_795)=A_794 | ~v1_funct_2(C_795, A_794, B_793) | ~m1_subset_1(C_795, k1_zfmisc_1(k2_zfmisc_1(A_794, B_793))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_9223, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_9210])).
% 9.14/3.21  tff(c_9234, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_7736, c_9223])).
% 9.14/3.21  tff(c_9236, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_9234])).
% 9.14/3.21  tff(c_9249, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_6', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_9236, c_36])).
% 9.14/3.21  tff(c_9272, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_6', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_9249])).
% 9.14/3.21  tff(c_8485, plain, (![A_741, B_742, C_743, D_744]: (k2_partfun1(A_741, B_742, C_743, D_744)=k7_relat_1(C_743, D_744) | ~m1_subset_1(C_743, k1_zfmisc_1(k2_zfmisc_1(A_741, B_742))) | ~v1_funct_1(C_743))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.14/3.21  tff(c_8494, plain, (![D_744]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_744)=k7_relat_1('#skF_6', D_744) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_8485])).
% 9.14/3.21  tff(c_8503, plain, (![D_744]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_744)=k7_relat_1('#skF_6', D_744))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_8494])).
% 9.14/3.21  tff(c_9355, plain, (![A_797, B_798, C_799, D_800]: (m1_subset_1(k2_partfun1(A_797, B_798, C_799, D_800), k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))) | ~m1_subset_1(C_799, k1_zfmisc_1(k2_zfmisc_1(A_797, B_798))) | ~v1_funct_1(C_799))), inference(cnfTransformation, [status(thm)], [f_135])).
% 9.14/3.21  tff(c_9390, plain, (![D_744]: (m1_subset_1(k7_relat_1('#skF_6', D_744), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))) | ~v1_funct_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_8503, c_9355])).
% 9.14/3.21  tff(c_9551, plain, (![D_808]: (m1_subset_1(k7_relat_1('#skF_6', D_808), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_76, c_9390])).
% 9.14/3.21  tff(c_9598, plain, (![D_808]: (v1_relat_1(k7_relat_1('#skF_6', D_808)))), inference(resolution, [status(thm)], [c_9551, c_38])).
% 9.14/3.21  tff(c_50, plain, (![C_41, A_39, B_40]: (m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | ~r1_tarski(k2_relat_1(C_41), B_40) | ~r1_tarski(k1_relat_1(C_41), A_39) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.14/3.21  tff(c_7236, plain, (~m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitLeft, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_8507, plain, (~m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_8503, c_7236])).
% 9.14/3.21  tff(c_8524, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_50, c_8507])).
% 9.14/3.21  tff(c_9799, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_9598, c_8524])).
% 9.14/3.21  tff(c_9800, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_9799])).
% 9.14/3.21  tff(c_9967, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9272, c_9800])).
% 9.14/3.21  tff(c_9979, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_14, c_9967])).
% 9.14/3.21  tff(c_9980, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_6', '#skF_3')), '#skF_4')), inference(splitRight, [status(thm)], [c_9799])).
% 9.14/3.21  tff(c_10126, plain, (~r1_tarski(k9_relat_1('#skF_6', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_34, c_9980])).
% 9.14/3.21  tff(c_10130, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_14, c_8225, c_10126])).
% 9.14/3.21  tff(c_10131, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_9234])).
% 9.14/3.21  tff(c_10181, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10131, c_8])).
% 9.14/3.21  tff(c_10183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_10181])).
% 9.14/3.21  tff(c_10185, plain, (m1_subset_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(splitRight, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_10510, plain, (![C_890, B_891, A_892]: (v1_xboole_0(C_890) | ~m1_subset_1(C_890, k1_zfmisc_1(k2_zfmisc_1(B_891, A_892))) | ~v1_xboole_0(A_892))), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.14/3.21  tff(c_10527, plain, (v1_xboole_0(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')) | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_10185, c_10510])).
% 9.14/3.21  tff(c_10569, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_10527])).
% 9.14/3.21  tff(c_10881, plain, (![A_910, B_911, C_912]: (k1_relset_1(A_910, B_911, C_912)=k1_relat_1(C_912) | ~m1_subset_1(C_912, k1_zfmisc_1(k2_zfmisc_1(A_910, B_911))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.21  tff(c_10900, plain, (k1_relset_1('#skF_2', '#skF_5', '#skF_6')=k1_relat_1('#skF_6')), inference(resolution, [status(thm)], [c_76, c_10881])).
% 9.14/3.21  tff(c_12421, plain, (![B_1014, A_1015, C_1016]: (k1_xboole_0=B_1014 | k1_relset_1(A_1015, B_1014, C_1016)=A_1015 | ~v1_funct_2(C_1016, A_1015, B_1014) | ~m1_subset_1(C_1016, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1014))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_12440, plain, (k1_xboole_0='#skF_5' | k1_relset_1('#skF_2', '#skF_5', '#skF_6')='#skF_2' | ~v1_funct_2('#skF_6', '#skF_2', '#skF_5')), inference(resolution, [status(thm)], [c_76, c_12421])).
% 9.14/3.21  tff(c_12454, plain, (k1_xboole_0='#skF_5' | k1_relat_1('#skF_6')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_10900, c_12440])).
% 9.14/3.21  tff(c_12456, plain, (k1_relat_1('#skF_6')='#skF_2'), inference(splitLeft, [status(thm)], [c_12454])).
% 9.14/3.21  tff(c_12476, plain, (![A_20]: (k1_relat_1(k7_relat_1('#skF_6', A_20))=A_20 | ~r1_tarski(A_20, '#skF_2') | ~v1_relat_1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_12456, c_36])).
% 9.14/3.21  tff(c_12981, plain, (![A_1039]: (k1_relat_1(k7_relat_1('#skF_6', A_1039))=A_1039 | ~r1_tarski(A_1039, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_12476])).
% 9.14/3.21  tff(c_11852, plain, (![A_982, B_983, C_984, D_985]: (k2_partfun1(A_982, B_983, C_984, D_985)=k7_relat_1(C_984, D_985) | ~m1_subset_1(C_984, k1_zfmisc_1(k2_zfmisc_1(A_982, B_983))) | ~v1_funct_1(C_984))), inference(cnfTransformation, [status(thm)], [f_141])).
% 9.14/3.21  tff(c_11861, plain, (![D_985]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_985)=k7_relat_1('#skF_6', D_985) | ~v1_funct_1('#skF_6'))), inference(resolution, [status(thm)], [c_76, c_11852])).
% 9.14/3.21  tff(c_11872, plain, (![D_985]: (k2_partfun1('#skF_2', '#skF_5', '#skF_6', D_985)=k7_relat_1('#skF_6', D_985))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_11861])).
% 9.14/3.21  tff(c_10898, plain, (k1_relset_1('#skF_3', '#skF_4', k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(resolution, [status(thm)], [c_10185, c_10881])).
% 9.14/3.21  tff(c_12036, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11872, c_11872, c_10898])).
% 9.14/3.21  tff(c_10184, plain, (~v1_funct_2(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_1338])).
% 9.14/3.21  tff(c_12042, plain, (~v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11872, c_10184])).
% 9.14/3.21  tff(c_12041, plain, (m1_subset_1(k7_relat_1('#skF_6', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_11872, c_10185])).
% 9.14/3.21  tff(c_12196, plain, (![B_1001, C_1002, A_1003]: (k1_xboole_0=B_1001 | v1_funct_2(C_1002, A_1003, B_1001) | k1_relset_1(A_1003, B_1001, C_1002)!=A_1003 | ~m1_subset_1(C_1002, k1_zfmisc_1(k2_zfmisc_1(A_1003, B_1001))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_12199, plain, (k1_xboole_0='#skF_4' | v1_funct_2(k7_relat_1('#skF_6', '#skF_3'), '#skF_3', '#skF_4') | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_12041, c_12196])).
% 9.14/3.21  tff(c_12221, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_12042, c_12199])).
% 9.14/3.21  tff(c_12227, plain, (k1_relset_1('#skF_3', '#skF_4', k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(splitLeft, [status(thm)], [c_12221])).
% 9.14/3.21  tff(c_12238, plain, (k1_relat_1(k7_relat_1('#skF_6', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12036, c_12227])).
% 9.14/3.21  tff(c_12993, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12981, c_12238])).
% 9.14/3.21  tff(c_13061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_12993])).
% 9.14/3.21  tff(c_13062, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_12454])).
% 9.14/3.21  tff(c_13116, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13062, c_8])).
% 9.14/3.21  tff(c_13118, plain, $false, inference(negUnitSimplification, [status(thm)], [c_82, c_13116])).
% 9.14/3.21  tff(c_13119, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_12221])).
% 9.14/3.21  tff(c_13170, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13119, c_8])).
% 9.14/3.21  tff(c_13172, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10569, c_13170])).
% 9.14/3.21  tff(c_13174, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_10527])).
% 9.14/3.21  tff(c_10187, plain, (![C_830, B_831, A_832]: (~v1_xboole_0(C_830) | ~m1_subset_1(B_831, k1_zfmisc_1(C_830)) | ~r2_hidden(A_832, B_831))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.14/3.21  tff(c_10195, plain, (![B_833, A_834, A_835]: (~v1_xboole_0(B_833) | ~r2_hidden(A_834, A_835) | ~r1_tarski(A_835, B_833))), inference(resolution, [status(thm)], [c_26, c_10187])).
% 9.14/3.21  tff(c_10219, plain, (![B_839, A_840, B_841]: (~v1_xboole_0(B_839) | ~r1_tarski(A_840, B_839) | r1_tarski(A_840, B_841))), inference(resolution, [status(thm)], [c_6, c_10195])).
% 9.14/3.21  tff(c_10233, plain, (![B_842, B_843]: (~v1_xboole_0(B_842) | r1_tarski(B_842, B_843))), inference(resolution, [status(thm)], [c_14, c_10219])).
% 9.14/3.21  tff(c_16, plain, (![A_8]: (k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.14/3.21  tff(c_10262, plain, (![B_842]: (k1_xboole_0=B_842 | ~v1_xboole_0(B_842))), inference(resolution, [status(thm)], [c_10233, c_16])).
% 9.14/3.21  tff(c_13258, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_13174, c_10262])).
% 9.14/3.21  tff(c_1363, plain, (![A_201, A_202, B_203]: (v1_relat_1(A_201) | ~r1_tarski(A_201, k2_zfmisc_1(A_202, B_203)))), inference(resolution, [status(thm)], [c_26, c_146])).
% 9.14/3.21  tff(c_1377, plain, (![A_202, B_203]: (v1_relat_1(k2_zfmisc_1(A_202, B_203)))), inference(resolution, [status(thm)], [c_14, c_1363])).
% 9.14/3.21  tff(c_22, plain, (![B_10]: (k2_zfmisc_1(k1_xboole_0, B_10)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.14/3.21  tff(c_10354, plain, (![C_862, A_863, B_864]: (v4_relat_1(C_862, A_863) | ~m1_subset_1(C_862, k1_zfmisc_1(k2_zfmisc_1(A_863, B_864))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 9.14/3.21  tff(c_10464, plain, (![A_885, A_886, B_887]: (v4_relat_1(A_885, A_886) | ~r1_tarski(A_885, k2_zfmisc_1(A_886, B_887)))), inference(resolution, [status(thm)], [c_26, c_10354])).
% 9.14/3.21  tff(c_10496, plain, (![A_888, B_889]: (v4_relat_1(k2_zfmisc_1(A_888, B_889), A_888))), inference(resolution, [status(thm)], [c_14, c_10464])).
% 9.14/3.21  tff(c_10199, plain, (![B_836, A_837]: (r1_tarski(k1_relat_1(B_836), A_837) | ~v4_relat_1(B_836, A_837) | ~v1_relat_1(B_836))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.14/3.21  tff(c_10217, plain, (![B_836]: (k1_relat_1(B_836)=k1_xboole_0 | ~v4_relat_1(B_836, k1_xboole_0) | ~v1_relat_1(B_836))), inference(resolution, [status(thm)], [c_10199, c_16])).
% 9.14/3.21  tff(c_10500, plain, (![B_889]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_889))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_889)))), inference(resolution, [status(thm)], [c_10496, c_10217])).
% 9.14/3.21  tff(c_10509, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_22, c_10500])).
% 9.14/3.21  tff(c_13261, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_13258, c_10509])).
% 9.14/3.21  tff(c_158, plain, (![A_11, A_67, B_68]: (v1_relat_1(A_11) | ~r1_tarski(A_11, k2_zfmisc_1(A_67, B_68)))), inference(resolution, [status(thm)], [c_26, c_146])).
% 9.14/3.21  tff(c_10258, plain, (![B_842]: (v1_relat_1(B_842) | ~v1_xboole_0(B_842))), inference(resolution, [status(thm)], [c_10233, c_158])).
% 9.14/3.21  tff(c_13259, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_13174, c_10258])).
% 9.14/3.21  tff(c_20, plain, (![A_9]: (k2_zfmisc_1(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.14/3.21  tff(c_10506, plain, (![A_9]: (v4_relat_1(k1_xboole_0, A_9))), inference(superposition, [status(thm), theory('equality')], [c_20, c_10496])).
% 9.14/3.21  tff(c_13260, plain, (![A_9]: (v4_relat_1('#skF_4', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_10506])).
% 9.14/3.21  tff(c_32, plain, (![B_17, A_16]: (r1_tarski(k1_relat_1(B_17), A_16) | ~v4_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.14/3.21  tff(c_13396, plain, (![A_16]: (r1_tarski('#skF_4', A_16) | ~v4_relat_1('#skF_4', A_16) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_13261, c_32])).
% 9.14/3.21  tff(c_13406, plain, (![A_16]: (r1_tarski('#skF_4', A_16))), inference(demodulation, [status(thm), theory('equality')], [c_13259, c_13260, c_13396])).
% 9.14/3.21  tff(c_13788, plain, (![A_1070, B_1071, C_1072]: (k1_relset_1(A_1070, B_1071, C_1072)=k1_relat_1(C_1072) | ~m1_subset_1(C_1072, k1_zfmisc_1(k2_zfmisc_1(A_1070, B_1071))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 9.14/3.21  tff(c_15078, plain, (![A_1147, B_1148, A_1149]: (k1_relset_1(A_1147, B_1148, A_1149)=k1_relat_1(A_1149) | ~r1_tarski(A_1149, k2_zfmisc_1(A_1147, B_1148)))), inference(resolution, [status(thm)], [c_26, c_13788])).
% 9.14/3.21  tff(c_15091, plain, (![A_1147, B_1148]: (k1_relset_1(A_1147, B_1148, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_13406, c_15078])).
% 9.14/3.21  tff(c_15108, plain, (![A_1147, B_1148]: (k1_relset_1(A_1147, B_1148, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13261, c_15091])).
% 9.14/3.21  tff(c_13185, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_13174, c_10262])).
% 9.14/3.21  tff(c_52, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_42, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_85, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_52])).
% 9.14/3.21  tff(c_13175, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_85])).
% 9.14/3.21  tff(c_13239, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13185, c_13185, c_13175])).
% 9.14/3.21  tff(c_13242, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_26, c_13239])).
% 9.14/3.21  tff(c_13246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_13242])).
% 9.14/3.21  tff(c_13248, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_85])).
% 9.14/3.21  tff(c_13372, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_13258, c_13248])).
% 9.14/3.21  tff(c_56, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_43))))), inference(cnfTransformation, [status(thm)], [f_127])).
% 9.14/3.21  tff(c_84, plain, (![C_44, B_43]: (v1_funct_2(C_44, k1_xboole_0, B_43) | k1_relset_1(k1_xboole_0, B_43, C_44)!=k1_xboole_0 | ~m1_subset_1(C_44, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_56])).
% 9.14/3.21  tff(c_13855, plain, (![C_1079, B_1080]: (v1_funct_2(C_1079, '#skF_4', B_1080) | k1_relset_1('#skF_4', B_1080, C_1079)!='#skF_4' | ~m1_subset_1(C_1079, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_13258, c_13258, c_13258, c_84])).
% 9.14/3.21  tff(c_14705, plain, (![B_1135]: (v1_funct_2('#skF_4', '#skF_4', B_1135) | k1_relset_1('#skF_4', B_1135, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_13372, c_13855])).
% 9.14/3.21  tff(c_13247, plain, (![A_42]: (v1_funct_2(k1_xboole_0, A_42, k1_xboole_0) | k1_xboole_0=A_42)), inference(splitRight, [status(thm)], [c_85])).
% 9.14/3.21  tff(c_13542, plain, (![A_42]: (v1_funct_2('#skF_4', A_42, '#skF_4') | A_42='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_13258, c_13258, c_13247])).
% 9.14/3.21  tff(c_13173, plain, (v1_xboole_0(k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3'))), inference(splitRight, [status(thm)], [c_10527])).
% 9.14/3.21  tff(c_13268, plain, (![B_842]: (B_842='#skF_4' | ~v1_xboole_0(B_842))), inference(demodulation, [status(thm), theory('equality')], [c_13258, c_10262])).
% 9.14/3.21  tff(c_13640, plain, (k2_partfun1('#skF_2', '#skF_5', '#skF_6', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_13173, c_13268])).
% 9.14/3.21  tff(c_13758, plain, (~v1_funct_2('#skF_4', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13640, c_10184])).
% 9.14/3.21  tff(c_13773, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_13542, c_13758])).
% 9.14/3.21  tff(c_13774, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13773, c_13758])).
% 9.14/3.21  tff(c_14717, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_14705, c_13774])).
% 9.14/3.21  tff(c_15118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_15108, c_14717])).
% 9.14/3.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.14/3.21  
% 9.14/3.21  Inference rules
% 9.14/3.21  ----------------------
% 9.14/3.21  #Ref     : 0
% 9.14/3.21  #Sup     : 3366
% 9.14/3.21  #Fact    : 0
% 9.14/3.21  #Define  : 0
% 9.14/3.21  #Split   : 60
% 9.14/3.21  #Chain   : 0
% 9.14/3.21  #Close   : 0
% 9.14/3.21  
% 9.14/3.21  Ordering : KBO
% 9.14/3.21  
% 9.14/3.21  Simplification rules
% 9.14/3.21  ----------------------
% 9.14/3.21  #Subsume      : 683
% 9.14/3.21  #Demod        : 2609
% 9.14/3.21  #Tautology    : 1274
% 9.14/3.21  #SimpNegUnit  : 24
% 9.14/3.21  #BackRed      : 423
% 9.14/3.21  
% 9.14/3.21  #Partial instantiations: 0
% 9.14/3.21  #Strategies tried      : 1
% 9.14/3.21  
% 9.14/3.21  Timing (in seconds)
% 9.14/3.21  ----------------------
% 9.14/3.21  Preprocessing        : 0.35
% 9.14/3.21  Parsing              : 0.18
% 9.14/3.21  CNF conversion       : 0.03
% 9.14/3.21  Main loop            : 1.98
% 9.14/3.21  Inferencing          : 0.63
% 9.14/3.21  Reduction            : 0.71
% 9.14/3.21  Demodulation         : 0.49
% 9.14/3.21  BG Simplification    : 0.07
% 9.14/3.21  Subsumption          : 0.41
% 9.14/3.21  Abstraction          : 0.08
% 9.14/3.21  MUC search           : 0.00
% 9.14/3.21  Cooper               : 0.00
% 9.14/3.21  Total                : 2.41
% 9.14/3.21  Index Insertion      : 0.00
% 9.14/3.21  Index Deletion       : 0.00
% 9.14/3.22  Index Matching       : 0.00
% 9.14/3.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
