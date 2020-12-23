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
% DateTime   : Thu Dec  3 10:13:36 EST 2020

% Result     : Theorem 6.72s
% Output     : CNFRefutation 6.72s
% Verified   : 
% Statistics : Number of formulae       :  180 (1510 expanded)
%              Number of leaves         :   37 ( 490 expanded)
%              Depth                    :   15
%              Number of atoms          :  307 (4997 expanded)
%              Number of equality atoms :   92 (1877 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_119,axiom,(
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

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_133,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_127,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_115,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_123,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_115])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2006,plain,(
    ! [A_324,B_325,C_326] :
      ( k1_relset_1(A_324,B_325,C_326) = k1_relat_1(C_326)
      | ~ m1_subset_1(C_326,k1_zfmisc_1(k2_zfmisc_1(A_324,B_325))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_2020,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_2006])).

tff(c_2699,plain,(
    ! [B_399,A_400,C_401] :
      ( k1_xboole_0 = B_399
      | k1_relset_1(A_400,B_399,C_401) = A_400
      | ~ v1_funct_2(C_401,A_400,B_399)
      | ~ m1_subset_1(C_401,k1_zfmisc_1(k2_zfmisc_1(A_400,B_399))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2708,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_2699])).

tff(c_2720,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_2020,c_2708])).

tff(c_2721,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_2720])).

tff(c_28,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2741,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2721,c_28])).

tff(c_2753,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_2741])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_2351,plain,(
    ! [A_386,B_387,C_388,D_389] :
      ( k2_partfun1(A_386,B_387,C_388,D_389) = k7_relat_1(C_388,D_389)
      | ~ m1_subset_1(C_388,k1_zfmisc_1(k2_zfmisc_1(A_386,B_387)))
      | ~ v1_funct_1(C_388) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2357,plain,(
    ! [D_389] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_389) = k7_relat_1('#skF_4',D_389)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_2351])).

tff(c_2368,plain,(
    ! [D_389] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_389) = k7_relat_1('#skF_4',D_389) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_2357])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_683,plain,(
    ! [A_165,B_166,C_167] :
      ( k1_relset_1(A_165,B_166,C_167) = k1_relat_1(C_167)
      | ~ m1_subset_1(C_167,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_693,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_683])).

tff(c_1260,plain,(
    ! [B_248,A_249,C_250] :
      ( k1_xboole_0 = B_248
      | k1_relset_1(A_249,B_248,C_250) = A_249
      | ~ v1_funct_2(C_250,A_249,B_248)
      | ~ m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_249,B_248))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1266,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1260])).

tff(c_1276,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_693,c_1266])).

tff(c_1277,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_1276])).

tff(c_1300,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1277,c_28])).

tff(c_1314,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1300])).

tff(c_1201,plain,(
    ! [A_236,B_237,C_238,D_239] :
      ( k2_partfun1(A_236,B_237,C_238,D_239) = k7_relat_1(C_238,D_239)
      | ~ m1_subset_1(C_238,k1_zfmisc_1(k2_zfmisc_1(A_236,B_237)))
      | ~ v1_funct_1(C_238) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_1205,plain,(
    ! [D_239] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_239) = k7_relat_1('#skF_4',D_239)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_1201])).

tff(c_1213,plain,(
    ! [D_239] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_239) = k7_relat_1('#skF_4',D_239) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1205])).

tff(c_1495,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( m1_subset_1(k2_partfun1(A_270,B_271,C_272,D_273),k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_1520,plain,(
    ! [D_239] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_239),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1213,c_1495])).

tff(c_1539,plain,(
    ! [D_274] : m1_subset_1(k7_relat_1('#skF_4',D_274),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_1520])).

tff(c_30,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1583,plain,(
    ! [D_274] : v1_relat_1(k7_relat_1('#skF_4',D_274)) ),
    inference(resolution,[status(thm)],[c_1539,c_30])).

tff(c_32,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1581,plain,(
    ! [D_274] : v5_relat_1(k7_relat_1('#skF_4',D_274),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1539,c_32])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_985,plain,(
    ! [C_226,A_227,B_228] :
      ( m1_subset_1(C_226,k1_zfmisc_1(k2_zfmisc_1(A_227,B_228)))
      | ~ r1_tarski(k2_relat_1(C_226),B_228)
      | ~ r1_tarski(k1_relat_1(C_226),A_227)
      | ~ v1_relat_1(C_226) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_463,plain,(
    ! [A_124,B_125,C_126,D_127] :
      ( v1_funct_1(k2_partfun1(A_124,B_125,C_126,D_127))
      | ~ m1_subset_1(C_126,k1_zfmisc_1(k2_zfmisc_1(A_124,B_125)))
      | ~ v1_funct_1(C_126) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_465,plain,(
    ! [D_127] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_127))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_463])).

tff(c_472,plain,(
    ! [D_127] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_127)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_465])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_138,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_138])).

tff(c_476,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_479,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_1016,plain,
    ( ~ r1_tarski(k2_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_985,c_479])).

tff(c_1442,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_1213,c_1213,c_1016])).

tff(c_1443,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1442])).

tff(c_1446,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1443])).

tff(c_1450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_1446])).

tff(c_1451,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1442])).

tff(c_1750,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1451])).

tff(c_1753,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1750])).

tff(c_1757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1583,c_1581,c_1753])).

tff(c_1758,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1451])).

tff(c_1777,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1314,c_1758])).

tff(c_1780,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_1777])).

tff(c_1782,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_2019,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1782,c_2006])).

tff(c_2514,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2368,c_2368,c_2019])).

tff(c_1781,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_2522,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2368,c_1781])).

tff(c_2521,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2368,c_1782])).

tff(c_48,plain,(
    ! [B_36,C_37,A_35] :
      ( k1_xboole_0 = B_36
      | v1_funct_2(C_37,A_35,B_36)
      | k1_relset_1(A_35,B_36,C_37) != A_35
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2572,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2521,c_48])).

tff(c_2591,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2522,c_77,c_2572])).

tff(c_2820,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2514,c_2591])).

tff(c_2827,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_2753,c_2820])).

tff(c_2831,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2827])).

tff(c_2832,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2844,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2832,c_14])).

tff(c_2833,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_2838,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2833])).

tff(c_2868,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2844,c_2838,c_66])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2852,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2832,c_16])).

tff(c_5287,plain,(
    ! [C_708,A_709,B_710] :
      ( v1_relat_1(C_708)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_709,B_710))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5292,plain,(
    ! [C_711] :
      ( v1_relat_1(C_711)
      | ~ m1_subset_1(C_711,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_5287])).

tff(c_5296,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2868,c_5292])).

tff(c_5325,plain,(
    ! [C_726,A_727,B_728] :
      ( v4_relat_1(C_726,A_727)
      | ~ m1_subset_1(C_726,k1_zfmisc_1(k2_zfmisc_1(A_727,B_728))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5357,plain,(
    ! [C_730,A_731] :
      ( v4_relat_1(C_730,A_731)
      | ~ m1_subset_1(C_730,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_5325])).

tff(c_5362,plain,(
    ! [A_732] : v4_relat_1('#skF_4',A_732) ),
    inference(resolution,[status(thm)],[c_2868,c_5357])).

tff(c_24,plain,(
    ! [B_14,A_13] :
      ( k7_relat_1(B_14,A_13) = B_14
      | ~ v4_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_5365,plain,(
    ! [A_732] :
      ( k7_relat_1('#skF_4',A_732) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5362,c_24])).

tff(c_5368,plain,(
    ! [A_732] : k7_relat_1('#skF_4',A_732) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5296,c_5365])).

tff(c_6940,plain,(
    ! [A_893,B_894,C_895,D_896] :
      ( k2_partfun1(A_893,B_894,C_895,D_896) = k7_relat_1(C_895,D_896)
      | ~ m1_subset_1(C_895,k1_zfmisc_1(k2_zfmisc_1(A_893,B_894)))
      | ~ v1_funct_1(C_895) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_6945,plain,(
    ! [B_897,C_898,D_899] :
      ( k2_partfun1('#skF_1',B_897,C_898,D_899) = k7_relat_1(C_898,D_899)
      | ~ m1_subset_1(C_898,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_898) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_6940])).

tff(c_6949,plain,(
    ! [B_897,D_899] :
      ( k2_partfun1('#skF_1',B_897,'#skF_4',D_899) = k7_relat_1('#skF_4',D_899)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2868,c_6945])).

tff(c_6954,plain,(
    ! [B_897,D_899] : k2_partfun1('#skF_1',B_897,'#skF_4',D_899) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5368,c_6949])).

tff(c_5232,plain,(
    ! [A_696,B_697,C_698,D_699] :
      ( v1_funct_1(k2_partfun1(A_696,B_697,C_698,D_699))
      | ~ m1_subset_1(C_698,k1_zfmisc_1(k2_zfmisc_1(A_696,B_697)))
      | ~ v1_funct_1(C_698) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5237,plain,(
    ! [B_700,C_701,D_702] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_700,C_701,D_702))
      | ~ m1_subset_1(C_701,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_1(C_701) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_5232])).

tff(c_5239,plain,(
    ! [B_700,D_702] :
      ( v1_funct_1(k2_partfun1('#skF_1',B_700,'#skF_4',D_702))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2868,c_5237])).

tff(c_5242,plain,(
    ! [B_700,D_702] : v1_funct_1(k2_partfun1('#skF_1',B_700,'#skF_4',D_702)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_5239])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2870,plain,(
    ! [A_407] :
      ( A_407 = '#skF_1'
      | ~ r1_tarski(A_407,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2832,c_10])).

tff(c_2880,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_64,c_2870])).

tff(c_4482,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2838,c_2880,c_2838,c_2838,c_2880,c_2880,c_2838,c_2852,c_2880,c_2880,c_60])).

tff(c_4483,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4482])).

tff(c_5245,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5242,c_4483])).

tff(c_5246,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4482])).

tff(c_5305,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_5246])).

tff(c_6956,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6954,c_5305])).

tff(c_6960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_6956])).

tff(c_6962,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_5246])).

tff(c_5289,plain,(
    ! [C_708] :
      ( v1_relat_1(C_708)
      | ~ m1_subset_1(C_708,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_5287])).

tff(c_6966,plain,(
    v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_6962,c_5289])).

tff(c_6991,plain,(
    ! [C_906,A_907,B_908] :
      ( v4_relat_1(C_906,A_907)
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7033,plain,(
    ! [C_910,A_911] :
      ( v4_relat_1(C_910,A_911)
      | ~ m1_subset_1(C_910,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2844,c_6991])).

tff(c_7067,plain,(
    ! [A_914] : v4_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_914) ),
    inference(resolution,[status(thm)],[c_6962,c_7033])).

tff(c_7070,plain,(
    ! [A_914] :
      ( k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_914) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')
      | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_7067,c_24])).

tff(c_7241,plain,(
    ! [A_928] : k7_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),A_928) = k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6966,c_7070])).

tff(c_7074,plain,(
    ! [C_915,B_916,A_917] :
      ( v5_relat_1(C_915,B_916)
      | ~ m1_subset_1(C_915,k1_zfmisc_1(k2_zfmisc_1(A_917,B_916))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_7083,plain,(
    ! [C_918,B_919] :
      ( v5_relat_1(C_918,B_919)
      | ~ m1_subset_1(C_918,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_7074])).

tff(c_7089,plain,(
    ! [B_919] : v5_relat_1('#skF_4',B_919) ),
    inference(resolution,[status(thm)],[c_2868,c_7083])).

tff(c_7090,plain,(
    ! [B_920] : v5_relat_1('#skF_4',B_920) ),
    inference(resolution,[status(thm)],[c_2868,c_7083])).

tff(c_6974,plain,(
    ! [B_903,A_904] :
      ( r1_tarski(k2_relat_1(B_903),A_904)
      | ~ v5_relat_1(B_903,A_904)
      | ~ v1_relat_1(B_903) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2869,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2832,c_10])).

tff(c_6989,plain,(
    ! [B_903] :
      ( k2_relat_1(B_903) = '#skF_1'
      | ~ v5_relat_1(B_903,'#skF_1')
      | ~ v1_relat_1(B_903) ) ),
    inference(resolution,[status(thm)],[c_6974,c_2869])).

tff(c_7094,plain,
    ( k2_relat_1('#skF_4') = '#skF_1'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7090,c_6989])).

tff(c_7097,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5296,c_7094])).

tff(c_7101,plain,(
    ! [A_9] :
      ( r1_tarski('#skF_1',A_9)
      | ~ v5_relat_1('#skF_4',A_9)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7097,c_20])).

tff(c_7111,plain,(
    ! [A_9] : r1_tarski('#skF_1',A_9) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5296,c_7089,c_7101])).

tff(c_7178,plain,(
    ! [B_925,A_926] :
      ( k1_relat_1(k7_relat_1(B_925,A_926)) = A_926
      | ~ r1_tarski(A_926,k1_relat_1(B_925))
      | ~ v1_relat_1(B_925) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_7195,plain,(
    ! [B_925] :
      ( k1_relat_1(k7_relat_1(B_925,'#skF_1')) = '#skF_1'
      | ~ v1_relat_1(B_925) ) ),
    inference(resolution,[status(thm)],[c_7111,c_7178])).

tff(c_7247,plain,
    ( k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7241,c_7195])).

tff(c_7258,plain,(
    k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6966,c_7247])).

tff(c_7458,plain,(
    ! [A_941,B_942,C_943] :
      ( k1_relset_1(A_941,B_942,C_943) = k1_relat_1(C_943)
      | ~ m1_subset_1(C_943,k1_zfmisc_1(k2_zfmisc_1(A_941,B_942))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_7465,plain,(
    ! [B_944,C_945] :
      ( k1_relset_1('#skF_1',B_944,C_945) = k1_relat_1(C_945)
      | ~ m1_subset_1(C_945,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2852,c_7458])).

tff(c_7467,plain,(
    ! [B_944] : k1_relset_1('#skF_1',B_944,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = k1_relat_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(resolution,[status(thm)],[c_6962,c_7465])).

tff(c_7471,plain,(
    ! [B_944] : k1_relset_1('#skF_1',B_944,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7258,c_7467])).

tff(c_46,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_72,plain,(
    ! [C_37,B_36] :
      ( v1_funct_2(C_37,k1_xboole_0,B_36)
      | k1_relset_1(k1_xboole_0,B_36,C_37) != k1_xboole_0
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_46])).

tff(c_7727,plain,(
    ! [C_966,B_967] :
      ( v1_funct_2(C_966,'#skF_1',B_967)
      | k1_relset_1('#skF_1',B_967,C_966) != '#skF_1'
      | ~ m1_subset_1(C_966,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2832,c_2832,c_2832,c_2832,c_72])).

tff(c_7729,plain,(
    ! [B_967] :
      ( v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_967)
      | k1_relset_1('#skF_1',B_967,k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_6962,c_7727])).

tff(c_7734,plain,(
    ! [B_967] : v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1',B_967) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7471,c_7729])).

tff(c_6961,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_5246])).

tff(c_7754,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7734,c_6961])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:02:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.72/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.35  
% 6.72/2.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.35  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.72/2.35  
% 6.72/2.35  %Foreground sorts:
% 6.72/2.35  
% 6.72/2.35  
% 6.72/2.35  %Background operators:
% 6.72/2.35  
% 6.72/2.35  
% 6.72/2.35  %Foreground operators:
% 6.72/2.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.72/2.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.72/2.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.72/2.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.72/2.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.72/2.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.72/2.35  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.72/2.35  tff('#skF_2', type, '#skF_2': $i).
% 6.72/2.35  tff('#skF_3', type, '#skF_3': $i).
% 6.72/2.35  tff('#skF_1', type, '#skF_1': $i).
% 6.72/2.35  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.72/2.35  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.72/2.35  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.72/2.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.72/2.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.72/2.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.72/2.35  tff('#skF_4', type, '#skF_4': $i).
% 6.72/2.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.72/2.35  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.72/2.35  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.72/2.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.72/2.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.72/2.35  
% 6.72/2.38  tff(f_153, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.72/2.38  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.72/2.38  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.72/2.38  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.72/2.38  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.72/2.38  tff(f_133, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.72/2.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.72/2.38  tff(f_127, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.72/2.38  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.72/2.38  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.72/2.38  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.72/2.38  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.72/2.38  tff(f_47, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.72/2.38  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 6.72/2.38  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.72/2.38  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_115, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.72/2.38  tff(c_123, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_115])).
% 6.72/2.38  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 6.72/2.38  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_2006, plain, (![A_324, B_325, C_326]: (k1_relset_1(A_324, B_325, C_326)=k1_relat_1(C_326) | ~m1_subset_1(C_326, k1_zfmisc_1(k2_zfmisc_1(A_324, B_325))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.72/2.38  tff(c_2020, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_2006])).
% 6.72/2.38  tff(c_2699, plain, (![B_399, A_400, C_401]: (k1_xboole_0=B_399 | k1_relset_1(A_400, B_399, C_401)=A_400 | ~v1_funct_2(C_401, A_400, B_399) | ~m1_subset_1(C_401, k1_zfmisc_1(k2_zfmisc_1(A_400, B_399))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.72/2.38  tff(c_2708, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_2699])).
% 6.72/2.38  tff(c_2720, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_2020, c_2708])).
% 6.72/2.38  tff(c_2721, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_2720])).
% 6.72/2.38  tff(c_28, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.72/2.38  tff(c_2741, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2721, c_28])).
% 6.72/2.38  tff(c_2753, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_2741])).
% 6.72/2.38  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_2351, plain, (![A_386, B_387, C_388, D_389]: (k2_partfun1(A_386, B_387, C_388, D_389)=k7_relat_1(C_388, D_389) | ~m1_subset_1(C_388, k1_zfmisc_1(k2_zfmisc_1(A_386, B_387))) | ~v1_funct_1(C_388))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.72/2.38  tff(c_2357, plain, (![D_389]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_389)=k7_relat_1('#skF_4', D_389) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_2351])).
% 6.72/2.38  tff(c_2368, plain, (![D_389]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_389)=k7_relat_1('#skF_4', D_389))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_2357])).
% 6.72/2.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.72/2.38  tff(c_683, plain, (![A_165, B_166, C_167]: (k1_relset_1(A_165, B_166, C_167)=k1_relat_1(C_167) | ~m1_subset_1(C_167, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.72/2.38  tff(c_693, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_683])).
% 6.72/2.38  tff(c_1260, plain, (![B_248, A_249, C_250]: (k1_xboole_0=B_248 | k1_relset_1(A_249, B_248, C_250)=A_249 | ~v1_funct_2(C_250, A_249, B_248) | ~m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_249, B_248))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.72/2.38  tff(c_1266, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1260])).
% 6.72/2.38  tff(c_1276, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_693, c_1266])).
% 6.72/2.38  tff(c_1277, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_1276])).
% 6.72/2.38  tff(c_1300, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1277, c_28])).
% 6.72/2.38  tff(c_1314, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_123, c_1300])).
% 6.72/2.38  tff(c_1201, plain, (![A_236, B_237, C_238, D_239]: (k2_partfun1(A_236, B_237, C_238, D_239)=k7_relat_1(C_238, D_239) | ~m1_subset_1(C_238, k1_zfmisc_1(k2_zfmisc_1(A_236, B_237))) | ~v1_funct_1(C_238))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.72/2.38  tff(c_1205, plain, (![D_239]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_239)=k7_relat_1('#skF_4', D_239) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1201])).
% 6.72/2.38  tff(c_1213, plain, (![D_239]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_239)=k7_relat_1('#skF_4', D_239))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1205])).
% 6.72/2.38  tff(c_1495, plain, (![A_270, B_271, C_272, D_273]: (m1_subset_1(k2_partfun1(A_270, B_271, C_272, D_273), k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_1(C_272))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.72/2.38  tff(c_1520, plain, (![D_239]: (m1_subset_1(k7_relat_1('#skF_4', D_239), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1213, c_1495])).
% 6.72/2.38  tff(c_1539, plain, (![D_274]: (m1_subset_1(k7_relat_1('#skF_4', D_274), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_1520])).
% 6.72/2.38  tff(c_30, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.72/2.38  tff(c_1583, plain, (![D_274]: (v1_relat_1(k7_relat_1('#skF_4', D_274)))), inference(resolution, [status(thm)], [c_1539, c_30])).
% 6.72/2.38  tff(c_32, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.38  tff(c_1581, plain, (![D_274]: (v5_relat_1(k7_relat_1('#skF_4', D_274), '#skF_2'))), inference(resolution, [status(thm)], [c_1539, c_32])).
% 6.72/2.38  tff(c_20, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.38  tff(c_22, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.72/2.38  tff(c_985, plain, (![C_226, A_227, B_228]: (m1_subset_1(C_226, k1_zfmisc_1(k2_zfmisc_1(A_227, B_228))) | ~r1_tarski(k2_relat_1(C_226), B_228) | ~r1_tarski(k1_relat_1(C_226), A_227) | ~v1_relat_1(C_226))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.72/2.38  tff(c_463, plain, (![A_124, B_125, C_126, D_127]: (v1_funct_1(k2_partfun1(A_124, B_125, C_126, D_127)) | ~m1_subset_1(C_126, k1_zfmisc_1(k2_zfmisc_1(A_124, B_125))) | ~v1_funct_1(C_126))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.72/2.38  tff(c_465, plain, (![D_127]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_127)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_463])).
% 6.72/2.38  tff(c_472, plain, (![D_127]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_127)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_465])).
% 6.72/2.38  tff(c_60, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_153])).
% 6.72/2.38  tff(c_138, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 6.72/2.38  tff(c_475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_472, c_138])).
% 6.72/2.38  tff(c_476, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 6.72/2.38  tff(c_479, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_476])).
% 6.72/2.38  tff(c_1016, plain, (~r1_tarski(k2_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_985, c_479])).
% 6.72/2.38  tff(c_1442, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1213, c_1213, c_1213, c_1016])).
% 6.72/2.38  tff(c_1443, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1442])).
% 6.72/2.38  tff(c_1446, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1443])).
% 6.72/2.38  tff(c_1450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_123, c_1446])).
% 6.72/2.38  tff(c_1451, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1442])).
% 6.72/2.38  tff(c_1750, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1451])).
% 6.72/2.38  tff(c_1753, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1750])).
% 6.72/2.38  tff(c_1757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1583, c_1581, c_1753])).
% 6.72/2.38  tff(c_1758, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_1451])).
% 6.72/2.38  tff(c_1777, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1314, c_1758])).
% 6.72/2.38  tff(c_1780, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_1777])).
% 6.72/2.38  tff(c_1782, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_476])).
% 6.72/2.38  tff(c_2019, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1782, c_2006])).
% 6.72/2.38  tff(c_2514, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2368, c_2368, c_2019])).
% 6.72/2.38  tff(c_1781, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_476])).
% 6.72/2.38  tff(c_2522, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2368, c_1781])).
% 6.72/2.38  tff(c_2521, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2368, c_1782])).
% 6.72/2.38  tff(c_48, plain, (![B_36, C_37, A_35]: (k1_xboole_0=B_36 | v1_funct_2(C_37, A_35, B_36) | k1_relset_1(A_35, B_36, C_37)!=A_35 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.72/2.38  tff(c_2572, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_2521, c_48])).
% 6.72/2.38  tff(c_2591, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2522, c_77, c_2572])).
% 6.72/2.38  tff(c_2820, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2514, c_2591])).
% 6.72/2.38  tff(c_2827, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_2753, c_2820])).
% 6.72/2.38  tff(c_2831, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_2827])).
% 6.72/2.38  tff(c_2832, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 6.72/2.38  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.72/2.38  tff(c_2844, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2832, c_14])).
% 6.72/2.38  tff(c_2833, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 6.72/2.38  tff(c_2838, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2833])).
% 6.72/2.38  tff(c_2868, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2844, c_2838, c_66])).
% 6.72/2.38  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.72/2.38  tff(c_2852, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2832, c_16])).
% 6.72/2.38  tff(c_5287, plain, (![C_708, A_709, B_710]: (v1_relat_1(C_708) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_709, B_710))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.72/2.38  tff(c_5292, plain, (![C_711]: (v1_relat_1(C_711) | ~m1_subset_1(C_711, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_5287])).
% 6.72/2.38  tff(c_5296, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2868, c_5292])).
% 6.72/2.38  tff(c_5325, plain, (![C_726, A_727, B_728]: (v4_relat_1(C_726, A_727) | ~m1_subset_1(C_726, k1_zfmisc_1(k2_zfmisc_1(A_727, B_728))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.38  tff(c_5357, plain, (![C_730, A_731]: (v4_relat_1(C_730, A_731) | ~m1_subset_1(C_730, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2844, c_5325])).
% 6.72/2.38  tff(c_5362, plain, (![A_732]: (v4_relat_1('#skF_4', A_732))), inference(resolution, [status(thm)], [c_2868, c_5357])).
% 6.72/2.38  tff(c_24, plain, (![B_14, A_13]: (k7_relat_1(B_14, A_13)=B_14 | ~v4_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.72/2.38  tff(c_5365, plain, (![A_732]: (k7_relat_1('#skF_4', A_732)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5362, c_24])).
% 6.72/2.38  tff(c_5368, plain, (![A_732]: (k7_relat_1('#skF_4', A_732)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5296, c_5365])).
% 6.72/2.38  tff(c_6940, plain, (![A_893, B_894, C_895, D_896]: (k2_partfun1(A_893, B_894, C_895, D_896)=k7_relat_1(C_895, D_896) | ~m1_subset_1(C_895, k1_zfmisc_1(k2_zfmisc_1(A_893, B_894))) | ~v1_funct_1(C_895))), inference(cnfTransformation, [status(thm)], [f_133])).
% 6.72/2.38  tff(c_6945, plain, (![B_897, C_898, D_899]: (k2_partfun1('#skF_1', B_897, C_898, D_899)=k7_relat_1(C_898, D_899) | ~m1_subset_1(C_898, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_898))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_6940])).
% 6.72/2.38  tff(c_6949, plain, (![B_897, D_899]: (k2_partfun1('#skF_1', B_897, '#skF_4', D_899)=k7_relat_1('#skF_4', D_899) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2868, c_6945])).
% 6.72/2.38  tff(c_6954, plain, (![B_897, D_899]: (k2_partfun1('#skF_1', B_897, '#skF_4', D_899)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5368, c_6949])).
% 6.72/2.38  tff(c_5232, plain, (![A_696, B_697, C_698, D_699]: (v1_funct_1(k2_partfun1(A_696, B_697, C_698, D_699)) | ~m1_subset_1(C_698, k1_zfmisc_1(k2_zfmisc_1(A_696, B_697))) | ~v1_funct_1(C_698))), inference(cnfTransformation, [status(thm)], [f_127])).
% 6.72/2.38  tff(c_5237, plain, (![B_700, C_701, D_702]: (v1_funct_1(k2_partfun1('#skF_1', B_700, C_701, D_702)) | ~m1_subset_1(C_701, k1_zfmisc_1('#skF_1')) | ~v1_funct_1(C_701))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_5232])).
% 6.72/2.38  tff(c_5239, plain, (![B_700, D_702]: (v1_funct_1(k2_partfun1('#skF_1', B_700, '#skF_4', D_702)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_2868, c_5237])).
% 6.72/2.38  tff(c_5242, plain, (![B_700, D_702]: (v1_funct_1(k2_partfun1('#skF_1', B_700, '#skF_4', D_702)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_5239])).
% 6.72/2.38  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.72/2.38  tff(c_2870, plain, (![A_407]: (A_407='#skF_1' | ~r1_tarski(A_407, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2832, c_10])).
% 6.72/2.38  tff(c_2880, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_64, c_2870])).
% 6.72/2.38  tff(c_4482, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2838, c_2880, c_2838, c_2838, c_2880, c_2880, c_2838, c_2852, c_2880, c_2880, c_60])).
% 6.72/2.38  tff(c_4483, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(splitLeft, [status(thm)], [c_4482])).
% 6.72/2.38  tff(c_5245, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5242, c_4483])).
% 6.72/2.38  tff(c_5246, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4482])).
% 6.72/2.38  tff(c_5305, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_5246])).
% 6.72/2.38  tff(c_6956, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6954, c_5305])).
% 6.72/2.38  tff(c_6960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2868, c_6956])).
% 6.72/2.38  tff(c_6962, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_5246])).
% 6.72/2.38  tff(c_5289, plain, (![C_708]: (v1_relat_1(C_708) | ~m1_subset_1(C_708, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_5287])).
% 6.72/2.38  tff(c_6966, plain, (v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(resolution, [status(thm)], [c_6962, c_5289])).
% 6.72/2.38  tff(c_6991, plain, (![C_906, A_907, B_908]: (v4_relat_1(C_906, A_907) | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.38  tff(c_7033, plain, (![C_910, A_911]: (v4_relat_1(C_910, A_911) | ~m1_subset_1(C_910, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2844, c_6991])).
% 6.72/2.38  tff(c_7067, plain, (![A_914]: (v4_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_914))), inference(resolution, [status(thm)], [c_6962, c_7033])).
% 6.72/2.38  tff(c_7070, plain, (![A_914]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_914)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1') | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_7067, c_24])).
% 6.72/2.38  tff(c_7241, plain, (![A_928]: (k7_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), A_928)=k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_6966, c_7070])).
% 6.72/2.38  tff(c_7074, plain, (![C_915, B_916, A_917]: (v5_relat_1(C_915, B_916) | ~m1_subset_1(C_915, k1_zfmisc_1(k2_zfmisc_1(A_917, B_916))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.72/2.38  tff(c_7083, plain, (![C_918, B_919]: (v5_relat_1(C_918, B_919) | ~m1_subset_1(C_918, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_7074])).
% 6.72/2.38  tff(c_7089, plain, (![B_919]: (v5_relat_1('#skF_4', B_919))), inference(resolution, [status(thm)], [c_2868, c_7083])).
% 6.72/2.38  tff(c_7090, plain, (![B_920]: (v5_relat_1('#skF_4', B_920))), inference(resolution, [status(thm)], [c_2868, c_7083])).
% 6.72/2.38  tff(c_6974, plain, (![B_903, A_904]: (r1_tarski(k2_relat_1(B_903), A_904) | ~v5_relat_1(B_903, A_904) | ~v1_relat_1(B_903))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.72/2.38  tff(c_2869, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2832, c_10])).
% 6.72/2.38  tff(c_6989, plain, (![B_903]: (k2_relat_1(B_903)='#skF_1' | ~v5_relat_1(B_903, '#skF_1') | ~v1_relat_1(B_903))), inference(resolution, [status(thm)], [c_6974, c_2869])).
% 6.72/2.38  tff(c_7094, plain, (k2_relat_1('#skF_4')='#skF_1' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7090, c_6989])).
% 6.72/2.38  tff(c_7097, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5296, c_7094])).
% 6.72/2.38  tff(c_7101, plain, (![A_9]: (r1_tarski('#skF_1', A_9) | ~v5_relat_1('#skF_4', A_9) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_7097, c_20])).
% 6.72/2.38  tff(c_7111, plain, (![A_9]: (r1_tarski('#skF_1', A_9))), inference(demodulation, [status(thm), theory('equality')], [c_5296, c_7089, c_7101])).
% 6.72/2.38  tff(c_7178, plain, (![B_925, A_926]: (k1_relat_1(k7_relat_1(B_925, A_926))=A_926 | ~r1_tarski(A_926, k1_relat_1(B_925)) | ~v1_relat_1(B_925))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.72/2.38  tff(c_7195, plain, (![B_925]: (k1_relat_1(k7_relat_1(B_925, '#skF_1'))='#skF_1' | ~v1_relat_1(B_925))), inference(resolution, [status(thm)], [c_7111, c_7178])).
% 6.72/2.38  tff(c_7247, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1' | ~v1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_7241, c_7195])).
% 6.72/2.38  tff(c_7258, plain, (k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6966, c_7247])).
% 6.72/2.38  tff(c_7458, plain, (![A_941, B_942, C_943]: (k1_relset_1(A_941, B_942, C_943)=k1_relat_1(C_943) | ~m1_subset_1(C_943, k1_zfmisc_1(k2_zfmisc_1(A_941, B_942))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.72/2.38  tff(c_7465, plain, (![B_944, C_945]: (k1_relset_1('#skF_1', B_944, C_945)=k1_relat_1(C_945) | ~m1_subset_1(C_945, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2852, c_7458])).
% 6.72/2.38  tff(c_7467, plain, (![B_944]: (k1_relset_1('#skF_1', B_944, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1')))), inference(resolution, [status(thm)], [c_6962, c_7465])).
% 6.72/2.38  tff(c_7471, plain, (![B_944]: (k1_relset_1('#skF_1', B_944, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7258, c_7467])).
% 6.72/2.38  tff(c_46, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_36))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.72/2.38  tff(c_72, plain, (![C_37, B_36]: (v1_funct_2(C_37, k1_xboole_0, B_36) | k1_relset_1(k1_xboole_0, B_36, C_37)!=k1_xboole_0 | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_46])).
% 6.72/2.38  tff(c_7727, plain, (![C_966, B_967]: (v1_funct_2(C_966, '#skF_1', B_967) | k1_relset_1('#skF_1', B_967, C_966)!='#skF_1' | ~m1_subset_1(C_966, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_2832, c_2832, c_2832, c_2832, c_72])).
% 6.72/2.38  tff(c_7729, plain, (![B_967]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_967) | k1_relset_1('#skF_1', B_967, k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))!='#skF_1')), inference(resolution, [status(thm)], [c_6962, c_7727])).
% 6.72/2.38  tff(c_7734, plain, (![B_967]: (v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', B_967))), inference(demodulation, [status(thm), theory('equality')], [c_7471, c_7729])).
% 6.72/2.38  tff(c_6961, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_5246])).
% 6.72/2.38  tff(c_7754, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7734, c_6961])).
% 6.72/2.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.72/2.38  
% 6.72/2.38  Inference rules
% 6.72/2.38  ----------------------
% 6.72/2.38  #Ref     : 0
% 6.72/2.38  #Sup     : 1672
% 6.72/2.38  #Fact    : 0
% 6.72/2.38  #Define  : 0
% 6.72/2.38  #Split   : 27
% 6.72/2.38  #Chain   : 0
% 6.72/2.38  #Close   : 0
% 6.72/2.38  
% 6.72/2.38  Ordering : KBO
% 6.72/2.38  
% 6.72/2.38  Simplification rules
% 6.72/2.38  ----------------------
% 6.72/2.38  #Subsume      : 294
% 6.72/2.38  #Demod        : 1272
% 6.72/2.38  #Tautology    : 669
% 6.72/2.38  #SimpNegUnit  : 17
% 6.72/2.38  #BackRed      : 28
% 6.72/2.38  
% 6.72/2.38  #Partial instantiations: 0
% 6.72/2.38  #Strategies tried      : 1
% 6.72/2.38  
% 6.72/2.38  Timing (in seconds)
% 6.72/2.38  ----------------------
% 6.72/2.38  Preprocessing        : 0.35
% 6.72/2.38  Parsing              : 0.18
% 6.72/2.38  CNF conversion       : 0.02
% 6.72/2.38  Main loop            : 1.24
% 6.72/2.38  Inferencing          : 0.47
% 6.72/2.38  Reduction            : 0.38
% 6.72/2.38  Demodulation         : 0.26
% 6.72/2.38  BG Simplification    : 0.05
% 6.72/2.38  Subsumption          : 0.24
% 6.72/2.38  Abstraction          : 0.05
% 6.72/2.38  MUC search           : 0.00
% 6.72/2.38  Cooper               : 0.00
% 6.72/2.38  Total                : 1.65
% 6.72/2.38  Index Insertion      : 0.00
% 6.72/2.38  Index Deletion       : 0.00
% 6.72/2.38  Index Matching       : 0.00
% 6.72/2.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
