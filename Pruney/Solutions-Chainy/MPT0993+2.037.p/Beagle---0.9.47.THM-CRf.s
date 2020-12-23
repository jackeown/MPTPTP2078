%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:47 EST 2020

% Result     : Theorem 5.73s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :  152 ( 685 expanded)
%              Number of leaves         :   38 ( 229 expanded)
%              Depth                    :   13
%              Number of atoms          :  251 (1566 expanded)
%              Number of equality atoms :   94 ( 519 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(A,C)
         => r2_relset_1(A,B,k2_partfun1(A,B,D,C),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_funct_2)).

tff(f_94,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_112,axiom,(
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

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_118,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1274,plain,(
    ! [A_200,B_201,D_202] :
      ( r2_relset_1(A_200,B_201,D_202,D_202)
      | ~ m1_subset_1(D_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_1288,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1274])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_158,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_164,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_158])).

tff(c_171,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_164])).

tff(c_102,plain,(
    ! [A_47,B_48] :
      ( r1_tarski(A_47,B_48)
      | ~ m1_subset_1(A_47,k1_zfmisc_1(B_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_109,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_60,c_102])).

tff(c_274,plain,(
    ! [A_77,C_78,B_79] :
      ( r1_tarski(A_77,C_78)
      | ~ r1_tarski(B_79,C_78)
      | ~ r1_tarski(A_77,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_283,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_109,c_274])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( m1_subset_1(A_9,k1_zfmisc_1(B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1914,plain,(
    ! [B_281,C_282,A_283] :
      ( k1_xboole_0 = B_281
      | v1_funct_2(C_282,A_283,B_281)
      | k1_relset_1(A_283,B_281,C_282) != A_283
      | ~ m1_subset_1(C_282,k1_zfmisc_1(k2_zfmisc_1(A_283,B_281))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1999,plain,(
    ! [B_295,A_296,A_297] :
      ( k1_xboole_0 = B_295
      | v1_funct_2(A_296,A_297,B_295)
      | k1_relset_1(A_297,B_295,A_296) != A_297
      | ~ r1_tarski(A_296,k2_zfmisc_1(A_297,B_295)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1914])).

tff(c_2020,plain,(
    ! [A_77] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(A_77,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',A_77) != '#skF_1'
      | ~ r1_tarski(A_77,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_283,c_1999])).

tff(c_2051,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2020])).

tff(c_16,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_110,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(resolution,[status(thm)],[c_16,c_102])).

tff(c_2088,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_110])).

tff(c_12,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2090,plain,(
    ! [A_6] : k2_zfmisc_1(A_6,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2051,c_2051,c_12])).

tff(c_128,plain,(
    ! [B_54,A_55] :
      ( B_54 = A_55
      | ~ r1_tarski(B_54,A_55)
      | ~ r1_tarski(A_55,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_137,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_109,c_128])).

tff(c_217,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_2366,plain,(
    ~ r1_tarski('#skF_2','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2090,c_217])).

tff(c_2375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2088,c_2366])).

tff(c_2377,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2020])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1366,plain,(
    ! [A_208,B_209,C_210] :
      ( k1_relset_1(A_208,B_209,C_210) = k1_relat_1(C_210)
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1385,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_1366])).

tff(c_2386,plain,(
    ! [B_317,A_318,C_319] :
      ( k1_xboole_0 = B_317
      | k1_relset_1(A_318,B_317,C_319) = A_318
      | ~ v1_funct_2(C_319,A_318,B_317)
      | ~ m1_subset_1(C_319,k1_zfmisc_1(k2_zfmisc_1(A_318,B_317))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_2393,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_2386])).

tff(c_2407,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1385,c_2393])).

tff(c_2408,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2377,c_2407])).

tff(c_58,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_286,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,'#skF_3')
      | ~ r1_tarski(A_77,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_274])).

tff(c_456,plain,(
    ! [B_102,A_103] :
      ( k7_relat_1(B_102,A_103) = B_102
      | ~ r1_tarski(k1_relat_1(B_102),A_103)
      | ~ v1_relat_1(B_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_470,plain,(
    ! [B_102] :
      ( k7_relat_1(B_102,'#skF_3') = B_102
      | ~ v1_relat_1(B_102)
      | ~ r1_tarski(k1_relat_1(B_102),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_286,c_456])).

tff(c_2425,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2408,c_470])).

tff(c_2441,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_171,c_2425])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1816,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( k2_partfun1(A_265,B_266,C_267,D_268) = k7_relat_1(C_267,D_268)
      | ~ m1_subset_1(C_267,k1_zfmisc_1(k2_zfmisc_1(A_265,B_266)))
      | ~ v1_funct_1(C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_1821,plain,(
    ! [D_268] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_268) = k7_relat_1('#skF_4',D_268)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1816])).

tff(c_1832,plain,(
    ! [D_268] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_268) = k7_relat_1('#skF_4',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1821])).

tff(c_56,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_1835,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1832,c_56])).

tff(c_2447,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2441,c_1835])).

tff(c_2450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1288,c_2447])).

tff(c_2451,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2476,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2451,c_60])).

tff(c_2836,plain,(
    ! [A_375,B_376,D_377] :
      ( r2_relset_1(A_375,B_376,D_377,D_377)
      | ~ m1_subset_1(D_377,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2863,plain,(
    ! [D_385] :
      ( r2_relset_1('#skF_1','#skF_2',D_385,D_385)
      | ~ m1_subset_1(D_385,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_2836])).

tff(c_2872,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2476,c_2863])).

tff(c_2889,plain,(
    ! [A_393,B_394,C_395] :
      ( k1_relset_1(A_393,B_394,C_395) = k1_relat_1(C_395)
      | ~ m1_subset_1(C_395,k1_zfmisc_1(k2_zfmisc_1(A_393,B_394))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_2937,plain,(
    ! [C_402] :
      ( k1_relset_1('#skF_1','#skF_2',C_402) = k1_relat_1(C_402)
      | ~ m1_subset_1(C_402,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_2889])).

tff(c_2949,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2476,c_2937])).

tff(c_3117,plain,(
    ! [B_428,C_429,A_430] :
      ( k1_xboole_0 = B_428
      | v1_funct_2(C_429,A_430,B_428)
      | k1_relset_1(A_430,B_428,C_429) != A_430
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(A_430,B_428))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3120,plain,(
    ! [C_429] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_429,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_429) != '#skF_1'
      | ~ m1_subset_1(C_429,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_3117])).

tff(c_3282,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3120])).

tff(c_10,plain,(
    ! [B_7,A_6] :
      ( k1_xboole_0 = B_7
      | k1_xboole_0 = A_6
      | k2_zfmisc_1(A_6,B_7) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2487,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_10])).

tff(c_2506,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2487])).

tff(c_3315,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3282,c_2506])).

tff(c_3408,plain,(
    ! [A_464] : k2_zfmisc_1(A_464,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3282,c_3282,c_12])).

tff(c_3448,plain,(
    '#skF_2' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3408,c_2451])).

tff(c_3469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3315,c_3448])).

tff(c_3471,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3120])).

tff(c_3221,plain,(
    ! [B_446,A_447,C_448] :
      ( k1_xboole_0 = B_446
      | k1_relset_1(A_447,B_446,C_448) = A_447
      | ~ v1_funct_2(C_448,A_447,B_446)
      | ~ m1_subset_1(C_448,k1_zfmisc_1(k2_zfmisc_1(A_447,B_446))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_3224,plain,(
    ! [C_448] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_448) = '#skF_1'
      | ~ v1_funct_2(C_448,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_448,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_3221])).

tff(c_3548,plain,(
    ! [C_475] :
      ( k1_relset_1('#skF_1','#skF_2',C_475) = '#skF_1'
      | ~ v1_funct_2(C_475,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_475,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_3471,c_3224])).

tff(c_3551,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2476,c_3548])).

tff(c_3562,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_2949,c_3551])).

tff(c_2518,plain,(
    ! [A_328,C_329,B_330] :
      ( r1_tarski(A_328,C_329)
      | ~ r1_tarski(B_330,C_329)
      | ~ r1_tarski(A_328,B_330) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2527,plain,(
    ! [A_328] :
      ( r1_tarski(A_328,'#skF_3')
      | ~ r1_tarski(A_328,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_58,c_2518])).

tff(c_2727,plain,(
    ! [B_358,A_359] :
      ( k7_relat_1(B_358,A_359) = B_358
      | ~ r1_tarski(k1_relat_1(B_358),A_359)
      | ~ v1_relat_1(B_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2736,plain,(
    ! [B_358] :
      ( k7_relat_1(B_358,'#skF_3') = B_358
      | ~ v1_relat_1(B_358)
      | ~ r1_tarski(k1_relat_1(B_358),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_2527,c_2727])).

tff(c_3571,plain,
    ( k7_relat_1('#skF_4','#skF_3') = '#skF_4'
    | ~ v1_relat_1('#skF_4')
    | ~ r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3562,c_2736])).

tff(c_3581,plain,(
    k7_relat_1('#skF_4','#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_171,c_3571])).

tff(c_3081,plain,(
    ! [A_420,B_421,C_422,D_423] :
      ( k2_partfun1(A_420,B_421,C_422,D_423) = k7_relat_1(C_422,D_423)
      | ~ m1_subset_1(C_422,k1_zfmisc_1(k2_zfmisc_1(A_420,B_421)))
      | ~ v1_funct_1(C_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_3163,plain,(
    ! [C_435,D_436] :
      ( k2_partfun1('#skF_1','#skF_2',C_435,D_436) = k7_relat_1(C_435,D_436)
      | ~ m1_subset_1(C_435,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2451,c_3081])).

tff(c_3165,plain,(
    ! [D_436] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_436) = k7_relat_1('#skF_4',D_436)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2476,c_3163])).

tff(c_3174,plain,(
    ! [D_436] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_436) = k7_relat_1('#skF_4',D_436) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3165])).

tff(c_3178,plain,(
    ~ r2_relset_1('#skF_1','#skF_2',k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3174,c_56])).

tff(c_3598,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3581,c_3178])).

tff(c_3601,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2872,c_3598])).

tff(c_3603,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2487])).

tff(c_3611,plain,(
    ! [A_8] : m1_subset_1('#skF_4',k1_zfmisc_1(A_8)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_16])).

tff(c_4412,plain,(
    ! [A_606,B_607,D_608] :
      ( r2_relset_1(A_606,B_607,D_608,D_608)
      | ~ m1_subset_1(D_608,k1_zfmisc_1(k2_zfmisc_1(A_606,B_607))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_4423,plain,(
    ! [A_606,B_607] : r2_relset_1(A_606,B_607,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3611,c_4412])).

tff(c_2453,plain,(
    ! [C_320,A_321,B_322] :
      ( v4_relat_1(C_320,A_321)
      | ~ m1_subset_1(C_320,k1_zfmisc_1(k2_zfmisc_1(A_321,B_322))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2473,plain,(
    ! [A_321] : v4_relat_1(k1_xboole_0,A_321) ),
    inference(resolution,[status(thm)],[c_16,c_2453])).

tff(c_3604,plain,(
    ! [A_321] : v4_relat_1('#skF_4',A_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_2473])).

tff(c_3621,plain,(
    ! [B_477,A_478] :
      ( k7_relat_1(B_477,A_478) = B_477
      | ~ v4_relat_1(B_477,A_478)
      | ~ v1_relat_1(B_477) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3624,plain,(
    ! [A_321] :
      ( k7_relat_1('#skF_4',A_321) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3604,c_3621])).

tff(c_3627,plain,(
    ! [A_321] : k7_relat_1('#skF_4',A_321) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_171,c_3624])).

tff(c_4650,plain,(
    ! [A_655,B_656,C_657,D_658] :
      ( k2_partfun1(A_655,B_656,C_657,D_658) = k7_relat_1(C_657,D_658)
      | ~ m1_subset_1(C_657,k1_zfmisc_1(k2_zfmisc_1(A_655,B_656)))
      | ~ v1_funct_1(C_657) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4655,plain,(
    ! [A_655,B_656,D_658] :
      ( k2_partfun1(A_655,B_656,'#skF_4',D_658) = k7_relat_1('#skF_4',D_658)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3611,c_4650])).

tff(c_4663,plain,(
    ! [A_655,B_656,D_658] : k2_partfun1(A_655,B_656,'#skF_4',D_658) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3627,c_4655])).

tff(c_3951,plain,(
    ! [A_524,B_525,D_526] :
      ( r2_relset_1(A_524,B_525,D_526,D_526)
      | ~ m1_subset_1(D_526,k1_zfmisc_1(k2_zfmisc_1(A_524,B_525))) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_3962,plain,(
    ! [A_524,B_525] : r2_relset_1(A_524,B_525,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_3611,c_3951])).

tff(c_4193,plain,(
    ! [A_573,B_574,C_575,D_576] :
      ( k2_partfun1(A_573,B_574,C_575,D_576) = k7_relat_1(C_575,D_576)
      | ~ m1_subset_1(C_575,k1_zfmisc_1(k2_zfmisc_1(A_573,B_574)))
      | ~ v1_funct_1(C_575) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_4196,plain,(
    ! [A_573,B_574,D_576] :
      ( k2_partfun1(A_573,B_574,'#skF_4',D_576) = k7_relat_1('#skF_4',D_576)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3611,c_4193])).

tff(c_4206,plain,(
    ! [A_573,B_574,D_576] : k2_partfun1(A_573,B_574,'#skF_4',D_576) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3627,c_4196])).

tff(c_3602,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2487])).

tff(c_3666,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3603,c_3603,c_3602])).

tff(c_3667,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3666])).

tff(c_3669,plain,(
    ~ r2_relset_1('#skF_1','#skF_4',k2_partfun1('#skF_1','#skF_4','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3667,c_3667,c_56])).

tff(c_4208,plain,(
    ~ r2_relset_1('#skF_1','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4206,c_3669])).

tff(c_4211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3962,c_4208])).

tff(c_4212,plain,(
    '#skF_1' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3666])).

tff(c_4216,plain,(
    ~ r2_relset_1('#skF_4','#skF_2',k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4212,c_4212,c_56])).

tff(c_4665,plain,(
    ~ r2_relset_1('#skF_4','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4663,c_4216])).

tff(c_4668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4423,c_4665])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:27:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.73/2.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.73/2.06  
% 5.73/2.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.07  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.80/2.07  
% 5.80/2.07  %Foreground sorts:
% 5.80/2.07  
% 5.80/2.07  
% 5.80/2.07  %Background operators:
% 5.80/2.07  
% 5.80/2.07  
% 5.80/2.07  %Foreground operators:
% 5.80/2.07  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.80/2.07  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.07  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 5.80/2.07  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.07  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.80/2.07  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.80/2.07  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.07  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.80/2.07  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.07  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.07  tff('#skF_1', type, '#skF_1': $i).
% 5.80/2.07  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.80/2.07  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.80/2.07  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.80/2.07  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.07  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.80/2.07  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.80/2.07  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.07  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.07  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.80/2.07  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.80/2.07  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.80/2.07  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.80/2.07  
% 5.80/2.09  tff(f_129, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(A, C) => r2_relset_1(A, B, k2_partfun1(A, B, D, C), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_funct_2)).
% 5.80/2.09  tff(f_94, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 5.80/2.09  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.09  tff(f_64, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.80/2.09  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 5.80/2.09  tff(f_49, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.80/2.09  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 5.80/2.09  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.80/2.09  tff(f_45, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 5.80/2.09  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.80/2.09  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.80/2.09  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.80/2.09  tff(f_118, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 5.80/2.09  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.80/2.09  tff(f_70, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.80/2.09  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.80/2.09  tff(c_1274, plain, (![A_200, B_201, D_202]: (r2_relset_1(A_200, B_201, D_202, D_202) | ~m1_subset_1(D_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.09  tff(c_1288, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_60, c_1274])).
% 5.80/2.09  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.09  tff(c_26, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.80/2.09  tff(c_158, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.80/2.09  tff(c_164, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_158])).
% 5.80/2.09  tff(c_171, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_164])).
% 5.80/2.09  tff(c_102, plain, (![A_47, B_48]: (r1_tarski(A_47, B_48) | ~m1_subset_1(A_47, k1_zfmisc_1(B_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.09  tff(c_109, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_60, c_102])).
% 5.80/2.09  tff(c_274, plain, (![A_77, C_78, B_79]: (r1_tarski(A_77, C_78) | ~r1_tarski(B_79, C_78) | ~r1_tarski(A_77, B_79))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.80/2.09  tff(c_283, plain, (![A_77]: (r1_tarski(A_77, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_109, c_274])).
% 5.80/2.09  tff(c_20, plain, (![A_9, B_10]: (m1_subset_1(A_9, k1_zfmisc_1(B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.80/2.09  tff(c_1914, plain, (![B_281, C_282, A_283]: (k1_xboole_0=B_281 | v1_funct_2(C_282, A_283, B_281) | k1_relset_1(A_283, B_281, C_282)!=A_283 | ~m1_subset_1(C_282, k1_zfmisc_1(k2_zfmisc_1(A_283, B_281))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.80/2.09  tff(c_1999, plain, (![B_295, A_296, A_297]: (k1_xboole_0=B_295 | v1_funct_2(A_296, A_297, B_295) | k1_relset_1(A_297, B_295, A_296)!=A_297 | ~r1_tarski(A_296, k2_zfmisc_1(A_297, B_295)))), inference(resolution, [status(thm)], [c_20, c_1914])).
% 5.80/2.09  tff(c_2020, plain, (![A_77]: (k1_xboole_0='#skF_2' | v1_funct_2(A_77, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', A_77)!='#skF_1' | ~r1_tarski(A_77, '#skF_4'))), inference(resolution, [status(thm)], [c_283, c_1999])).
% 5.80/2.09  tff(c_2051, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2020])).
% 5.80/2.09  tff(c_16, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.80/2.09  tff(c_110, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(resolution, [status(thm)], [c_16, c_102])).
% 5.80/2.09  tff(c_2088, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_2051, c_110])).
% 5.80/2.09  tff(c_12, plain, (![A_6]: (k2_zfmisc_1(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.80/2.09  tff(c_2090, plain, (![A_6]: (k2_zfmisc_1(A_6, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2051, c_2051, c_12])).
% 5.80/2.09  tff(c_128, plain, (![B_54, A_55]: (B_54=A_55 | ~r1_tarski(B_54, A_55) | ~r1_tarski(A_55, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.80/2.09  tff(c_137, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_109, c_128])).
% 5.80/2.09  tff(c_217, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_137])).
% 5.80/2.09  tff(c_2366, plain, (~r1_tarski('#skF_2', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2090, c_217])).
% 5.80/2.09  tff(c_2375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2088, c_2366])).
% 5.80/2.09  tff(c_2377, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_2020])).
% 5.80/2.09  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.80/2.09  tff(c_1366, plain, (![A_208, B_209, C_210]: (k1_relset_1(A_208, B_209, C_210)=k1_relat_1(C_210) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.80/2.09  tff(c_1385, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_1366])).
% 5.80/2.09  tff(c_2386, plain, (![B_317, A_318, C_319]: (k1_xboole_0=B_317 | k1_relset_1(A_318, B_317, C_319)=A_318 | ~v1_funct_2(C_319, A_318, B_317) | ~m1_subset_1(C_319, k1_zfmisc_1(k2_zfmisc_1(A_318, B_317))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.80/2.09  tff(c_2393, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_2386])).
% 5.80/2.09  tff(c_2407, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_1385, c_2393])).
% 5.80/2.09  tff(c_2408, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2377, c_2407])).
% 5.80/2.09  tff(c_58, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.80/2.09  tff(c_286, plain, (![A_77]: (r1_tarski(A_77, '#skF_3') | ~r1_tarski(A_77, '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_274])).
% 5.80/2.09  tff(c_456, plain, (![B_102, A_103]: (k7_relat_1(B_102, A_103)=B_102 | ~r1_tarski(k1_relat_1(B_102), A_103) | ~v1_relat_1(B_102))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.80/2.09  tff(c_470, plain, (![B_102]: (k7_relat_1(B_102, '#skF_3')=B_102 | ~v1_relat_1(B_102) | ~r1_tarski(k1_relat_1(B_102), '#skF_1'))), inference(resolution, [status(thm)], [c_286, c_456])).
% 5.80/2.09  tff(c_2425, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2408, c_470])).
% 5.80/2.09  tff(c_2441, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_171, c_2425])).
% 5.80/2.09  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.80/2.09  tff(c_1816, plain, (![A_265, B_266, C_267, D_268]: (k2_partfun1(A_265, B_266, C_267, D_268)=k7_relat_1(C_267, D_268) | ~m1_subset_1(C_267, k1_zfmisc_1(k2_zfmisc_1(A_265, B_266))) | ~v1_funct_1(C_267))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.80/2.09  tff(c_1821, plain, (![D_268]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_268)=k7_relat_1('#skF_4', D_268) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1816])).
% 5.80/2.09  tff(c_1832, plain, (![D_268]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_268)=k7_relat_1('#skF_4', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1821])).
% 5.80/2.09  tff(c_56, plain, (~r2_relset_1('#skF_1', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.80/2.09  tff(c_1835, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1832, c_56])).
% 5.80/2.09  tff(c_2447, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2441, c_1835])).
% 5.80/2.09  tff(c_2450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1288, c_2447])).
% 5.80/2.09  tff(c_2451, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_137])).
% 5.80/2.09  tff(c_2476, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2451, c_60])).
% 5.80/2.09  tff(c_2836, plain, (![A_375, B_376, D_377]: (r2_relset_1(A_375, B_376, D_377, D_377) | ~m1_subset_1(D_377, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.09  tff(c_2863, plain, (![D_385]: (r2_relset_1('#skF_1', '#skF_2', D_385, D_385) | ~m1_subset_1(D_385, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2451, c_2836])).
% 5.80/2.09  tff(c_2872, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2476, c_2863])).
% 5.80/2.09  tff(c_2889, plain, (![A_393, B_394, C_395]: (k1_relset_1(A_393, B_394, C_395)=k1_relat_1(C_395) | ~m1_subset_1(C_395, k1_zfmisc_1(k2_zfmisc_1(A_393, B_394))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.80/2.09  tff(c_2937, plain, (![C_402]: (k1_relset_1('#skF_1', '#skF_2', C_402)=k1_relat_1(C_402) | ~m1_subset_1(C_402, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2451, c_2889])).
% 5.80/2.09  tff(c_2949, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2476, c_2937])).
% 5.80/2.09  tff(c_3117, plain, (![B_428, C_429, A_430]: (k1_xboole_0=B_428 | v1_funct_2(C_429, A_430, B_428) | k1_relset_1(A_430, B_428, C_429)!=A_430 | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(A_430, B_428))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.80/2.09  tff(c_3120, plain, (![C_429]: (k1_xboole_0='#skF_2' | v1_funct_2(C_429, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_429)!='#skF_1' | ~m1_subset_1(C_429, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2451, c_3117])).
% 5.80/2.09  tff(c_3282, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_3120])).
% 5.80/2.09  tff(c_10, plain, (![B_7, A_6]: (k1_xboole_0=B_7 | k1_xboole_0=A_6 | k2_zfmisc_1(A_6, B_7)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.80/2.09  tff(c_2487, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2451, c_10])).
% 5.80/2.09  tff(c_2506, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2487])).
% 5.80/2.09  tff(c_3315, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3282, c_2506])).
% 5.80/2.09  tff(c_3408, plain, (![A_464]: (k2_zfmisc_1(A_464, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_3282, c_3282, c_12])).
% 5.80/2.09  tff(c_3448, plain, ('#skF_2'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_3408, c_2451])).
% 5.80/2.09  tff(c_3469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3315, c_3448])).
% 5.80/2.09  tff(c_3471, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_3120])).
% 5.80/2.09  tff(c_3221, plain, (![B_446, A_447, C_448]: (k1_xboole_0=B_446 | k1_relset_1(A_447, B_446, C_448)=A_447 | ~v1_funct_2(C_448, A_447, B_446) | ~m1_subset_1(C_448, k1_zfmisc_1(k2_zfmisc_1(A_447, B_446))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 5.80/2.09  tff(c_3224, plain, (![C_448]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_448)='#skF_1' | ~v1_funct_2(C_448, '#skF_1', '#skF_2') | ~m1_subset_1(C_448, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2451, c_3221])).
% 5.80/2.09  tff(c_3548, plain, (![C_475]: (k1_relset_1('#skF_1', '#skF_2', C_475)='#skF_1' | ~v1_funct_2(C_475, '#skF_1', '#skF_2') | ~m1_subset_1(C_475, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_3471, c_3224])).
% 5.80/2.09  tff(c_3551, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2476, c_3548])).
% 5.80/2.09  tff(c_3562, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_2949, c_3551])).
% 5.80/2.09  tff(c_2518, plain, (![A_328, C_329, B_330]: (r1_tarski(A_328, C_329) | ~r1_tarski(B_330, C_329) | ~r1_tarski(A_328, B_330))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.80/2.09  tff(c_2527, plain, (![A_328]: (r1_tarski(A_328, '#skF_3') | ~r1_tarski(A_328, '#skF_1'))), inference(resolution, [status(thm)], [c_58, c_2518])).
% 5.80/2.09  tff(c_2727, plain, (![B_358, A_359]: (k7_relat_1(B_358, A_359)=B_358 | ~r1_tarski(k1_relat_1(B_358), A_359) | ~v1_relat_1(B_358))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.80/2.09  tff(c_2736, plain, (![B_358]: (k7_relat_1(B_358, '#skF_3')=B_358 | ~v1_relat_1(B_358) | ~r1_tarski(k1_relat_1(B_358), '#skF_1'))), inference(resolution, [status(thm)], [c_2527, c_2727])).
% 5.80/2.09  tff(c_3571, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4' | ~v1_relat_1('#skF_4') | ~r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3562, c_2736])).
% 5.80/2.09  tff(c_3581, plain, (k7_relat_1('#skF_4', '#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_171, c_3571])).
% 5.80/2.09  tff(c_3081, plain, (![A_420, B_421, C_422, D_423]: (k2_partfun1(A_420, B_421, C_422, D_423)=k7_relat_1(C_422, D_423) | ~m1_subset_1(C_422, k1_zfmisc_1(k2_zfmisc_1(A_420, B_421))) | ~v1_funct_1(C_422))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.80/2.09  tff(c_3163, plain, (![C_435, D_436]: (k2_partfun1('#skF_1', '#skF_2', C_435, D_436)=k7_relat_1(C_435, D_436) | ~m1_subset_1(C_435, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_435))), inference(superposition, [status(thm), theory('equality')], [c_2451, c_3081])).
% 5.80/2.09  tff(c_3165, plain, (![D_436]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_436)=k7_relat_1('#skF_4', D_436) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2476, c_3163])).
% 5.80/2.09  tff(c_3174, plain, (![D_436]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_436)=k7_relat_1('#skF_4', D_436))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3165])).
% 5.80/2.09  tff(c_3178, plain, (~r2_relset_1('#skF_1', '#skF_2', k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3174, c_56])).
% 5.80/2.09  tff(c_3598, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3581, c_3178])).
% 5.80/2.09  tff(c_3601, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2872, c_3598])).
% 5.80/2.09  tff(c_3603, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2487])).
% 5.80/2.09  tff(c_3611, plain, (![A_8]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_8)))), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_16])).
% 5.80/2.09  tff(c_4412, plain, (![A_606, B_607, D_608]: (r2_relset_1(A_606, B_607, D_608, D_608) | ~m1_subset_1(D_608, k1_zfmisc_1(k2_zfmisc_1(A_606, B_607))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.09  tff(c_4423, plain, (![A_606, B_607]: (r2_relset_1(A_606, B_607, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3611, c_4412])).
% 5.80/2.09  tff(c_2453, plain, (![C_320, A_321, B_322]: (v4_relat_1(C_320, A_321) | ~m1_subset_1(C_320, k1_zfmisc_1(k2_zfmisc_1(A_321, B_322))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.80/2.09  tff(c_2473, plain, (![A_321]: (v4_relat_1(k1_xboole_0, A_321))), inference(resolution, [status(thm)], [c_16, c_2453])).
% 5.80/2.09  tff(c_3604, plain, (![A_321]: (v4_relat_1('#skF_4', A_321))), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_2473])).
% 5.80/2.09  tff(c_3621, plain, (![B_477, A_478]: (k7_relat_1(B_477, A_478)=B_477 | ~v4_relat_1(B_477, A_478) | ~v1_relat_1(B_477))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.80/2.09  tff(c_3624, plain, (![A_321]: (k7_relat_1('#skF_4', A_321)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_3604, c_3621])).
% 5.80/2.09  tff(c_3627, plain, (![A_321]: (k7_relat_1('#skF_4', A_321)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_171, c_3624])).
% 5.80/2.09  tff(c_4650, plain, (![A_655, B_656, C_657, D_658]: (k2_partfun1(A_655, B_656, C_657, D_658)=k7_relat_1(C_657, D_658) | ~m1_subset_1(C_657, k1_zfmisc_1(k2_zfmisc_1(A_655, B_656))) | ~v1_funct_1(C_657))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.80/2.09  tff(c_4655, plain, (![A_655, B_656, D_658]: (k2_partfun1(A_655, B_656, '#skF_4', D_658)=k7_relat_1('#skF_4', D_658) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3611, c_4650])).
% 5.80/2.09  tff(c_4663, plain, (![A_655, B_656, D_658]: (k2_partfun1(A_655, B_656, '#skF_4', D_658)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3627, c_4655])).
% 5.80/2.09  tff(c_3951, plain, (![A_524, B_525, D_526]: (r2_relset_1(A_524, B_525, D_526, D_526) | ~m1_subset_1(D_526, k1_zfmisc_1(k2_zfmisc_1(A_524, B_525))))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.80/2.09  tff(c_3962, plain, (![A_524, B_525]: (r2_relset_1(A_524, B_525, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_3611, c_3951])).
% 5.80/2.09  tff(c_4193, plain, (![A_573, B_574, C_575, D_576]: (k2_partfun1(A_573, B_574, C_575, D_576)=k7_relat_1(C_575, D_576) | ~m1_subset_1(C_575, k1_zfmisc_1(k2_zfmisc_1(A_573, B_574))) | ~v1_funct_1(C_575))), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.80/2.09  tff(c_4196, plain, (![A_573, B_574, D_576]: (k2_partfun1(A_573, B_574, '#skF_4', D_576)=k7_relat_1('#skF_4', D_576) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3611, c_4193])).
% 5.80/2.09  tff(c_4206, plain, (![A_573, B_574, D_576]: (k2_partfun1(A_573, B_574, '#skF_4', D_576)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3627, c_4196])).
% 5.80/2.09  tff(c_3602, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_2487])).
% 5.80/2.09  tff(c_3666, plain, ('#skF_1'='#skF_4' | '#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3603, c_3603, c_3602])).
% 5.80/2.09  tff(c_3667, plain, ('#skF_2'='#skF_4'), inference(splitLeft, [status(thm)], [c_3666])).
% 5.80/2.09  tff(c_3669, plain, (~r2_relset_1('#skF_1', '#skF_4', k2_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3667, c_3667, c_56])).
% 5.80/2.09  tff(c_4208, plain, (~r2_relset_1('#skF_1', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4206, c_3669])).
% 5.80/2.09  tff(c_4211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3962, c_4208])).
% 5.80/2.09  tff(c_4212, plain, ('#skF_1'='#skF_4'), inference(splitRight, [status(thm)], [c_3666])).
% 5.80/2.09  tff(c_4216, plain, (~r2_relset_1('#skF_4', '#skF_2', k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4212, c_4212, c_56])).
% 5.80/2.09  tff(c_4665, plain, (~r2_relset_1('#skF_4', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4663, c_4216])).
% 5.80/2.09  tff(c_4668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4423, c_4665])).
% 5.80/2.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.80/2.09  
% 5.80/2.09  Inference rules
% 5.80/2.09  ----------------------
% 5.80/2.09  #Ref     : 0
% 5.80/2.09  #Sup     : 959
% 5.80/2.09  #Fact    : 0
% 5.80/2.09  #Define  : 0
% 5.80/2.09  #Split   : 22
% 5.80/2.09  #Chain   : 0
% 5.80/2.09  #Close   : 0
% 5.80/2.09  
% 5.80/2.09  Ordering : KBO
% 5.80/2.09  
% 5.80/2.09  Simplification rules
% 5.80/2.09  ----------------------
% 5.80/2.09  #Subsume      : 217
% 5.80/2.09  #Demod        : 865
% 5.80/2.09  #Tautology    : 434
% 5.80/2.09  #SimpNegUnit  : 12
% 5.80/2.09  #BackRed      : 176
% 5.80/2.09  
% 5.80/2.09  #Partial instantiations: 0
% 5.80/2.09  #Strategies tried      : 1
% 5.80/2.09  
% 5.80/2.09  Timing (in seconds)
% 5.80/2.09  ----------------------
% 5.80/2.09  Preprocessing        : 0.34
% 5.80/2.09  Parsing              : 0.18
% 5.80/2.09  CNF conversion       : 0.02
% 5.80/2.09  Main loop            : 0.97
% 5.80/2.09  Inferencing          : 0.33
% 5.80/2.10  Reduction            : 0.34
% 5.80/2.10  Demodulation         : 0.24
% 5.80/2.10  BG Simplification    : 0.03
% 5.80/2.10  Subsumption          : 0.18
% 5.80/2.10  Abstraction          : 0.04
% 5.80/2.10  MUC search           : 0.00
% 5.80/2.10  Cooper               : 0.00
% 5.80/2.10  Total                : 1.36
% 5.80/2.10  Index Insertion      : 0.00
% 5.80/2.10  Index Deletion       : 0.00
% 5.80/2.10  Index Matching       : 0.00
% 5.80/2.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------
