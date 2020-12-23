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
% DateTime   : Thu Dec  3 10:13:31 EST 2020

% Result     : Theorem 7.08s
% Output     : CNFRefutation 7.41s
% Verified   : 
% Statistics : Number of formulae       :  199 (3193 expanded)
%              Number of leaves         :   39 ( 973 expanded)
%              Depth                    :   16
%              Number of atoms          :  323 (9801 expanded)
%              Number of equality atoms :   85 (3848 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_146,negated_conjecture,(
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

tff(f_76,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

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

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_126,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_120,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_64,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_173,plain,(
    ! [C_58,A_59,B_60] :
      ( v1_relat_1(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_186,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_173])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_77,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_3457,plain,(
    ! [A_429,B_430,C_431] :
      ( k1_relset_1(A_429,B_430,C_431) = k1_relat_1(C_431)
      | ~ m1_subset_1(C_431,k1_zfmisc_1(k2_zfmisc_1(A_429,B_430))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_3476,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_3457])).

tff(c_4182,plain,(
    ! [B_509,A_510,C_511] :
      ( k1_xboole_0 = B_509
      | k1_relset_1(A_510,B_509,C_511) = A_510
      | ~ v1_funct_2(C_511,A_510,B_509)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_510,B_509))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4195,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_4182])).

tff(c_4208,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3476,c_4195])).

tff(c_4209,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_4208])).

tff(c_30,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4218,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4209,c_30])).

tff(c_4224,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_4218])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_4067,plain,(
    ! [A_503,B_504,C_505,D_506] :
      ( k2_partfun1(A_503,B_504,C_505,D_506) = k7_relat_1(C_505,D_506)
      | ~ m1_subset_1(C_505,k1_zfmisc_1(k2_zfmisc_1(A_503,B_504)))
      | ~ v1_funct_1(C_505) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_4076,plain,(
    ! [D_506] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_506) = k7_relat_1('#skF_4',D_506)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_4067])).

tff(c_4088,plain,(
    ! [D_506] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_506) = k7_relat_1('#skF_4',D_506) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4076])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1352,plain,(
    ! [A_200,B_201,C_202] :
      ( k1_relset_1(A_200,B_201,C_202) = k1_relat_1(C_202)
      | ~ m1_subset_1(C_202,k1_zfmisc_1(k2_zfmisc_1(A_200,B_201))) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1367,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_1352])).

tff(c_1781,plain,(
    ! [B_261,A_262,C_263] :
      ( k1_xboole_0 = B_261
      | k1_relset_1(A_262,B_261,C_263) = A_262
      | ~ v1_funct_2(C_263,A_262,B_261)
      | ~ m1_subset_1(C_263,k1_zfmisc_1(k2_zfmisc_1(A_262,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_1791,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_1781])).

tff(c_1802,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1367,c_1791])).

tff(c_1803,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_1802])).

tff(c_1812,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1803,c_30])).

tff(c_1818,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_1812])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_797,plain,(
    ! [A_138,A_139,B_140] :
      ( v1_relat_1(A_138)
      | ~ r1_tarski(A_138,k2_zfmisc_1(A_139,B_140)) ) ),
    inference(resolution,[status(thm)],[c_18,c_173])).

tff(c_827,plain,(
    ! [A_139,B_140] : v1_relat_1(k2_zfmisc_1(A_139,B_140)) ),
    inference(resolution,[status(thm)],[c_6,c_797])).

tff(c_1577,plain,(
    ! [A_233,B_234,C_235,D_236] :
      ( k2_partfun1(A_233,B_234,C_235,D_236) = k7_relat_1(C_235,D_236)
      | ~ m1_subset_1(C_235,k1_zfmisc_1(k2_zfmisc_1(A_233,B_234)))
      | ~ v1_funct_1(C_235) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1582,plain,(
    ! [D_236] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_236) = k7_relat_1('#skF_4',D_236)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_1577])).

tff(c_1590,plain,(
    ! [D_236] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_236) = k7_relat_1('#skF_4',D_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_1582])).

tff(c_2179,plain,(
    ! [A_294,B_295,C_296,D_297] :
      ( m1_subset_1(k2_partfun1(A_294,B_295,C_296,D_297),k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ m1_subset_1(C_296,k1_zfmisc_1(k2_zfmisc_1(A_294,B_295)))
      | ~ v1_funct_1(C_296) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_2210,plain,(
    ! [D_236] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_236),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1590,c_2179])).

tff(c_2233,plain,(
    ! [D_298] : m1_subset_1(k7_relat_1('#skF_4',D_298),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_66,c_2210])).

tff(c_20,plain,(
    ! [B_10,A_8] :
      ( v1_relat_1(B_10)
      | ~ m1_subset_1(B_10,k1_zfmisc_1(A_8))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2255,plain,(
    ! [D_298] :
      ( v1_relat_1(k7_relat_1('#skF_4',D_298))
      | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_2233,c_20])).

tff(c_2279,plain,(
    ! [D_298] : v1_relat_1(k7_relat_1('#skF_4',D_298)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_827,c_2255])).

tff(c_34,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2275,plain,(
    ! [D_298] : v5_relat_1(k7_relat_1('#skF_4',D_298),'#skF_2') ),
    inference(resolution,[status(thm)],[c_2233,c_34])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(B_12),A_11)
      | ~ v5_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_865,plain,(
    ! [B_145,A_146] :
      ( v1_relat_1(B_145)
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_146))
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_899,plain,(
    ! [A_149,B_150] :
      ( v1_relat_1(A_149)
      | ~ v1_relat_1(B_150)
      | ~ r1_tarski(A_149,B_150) ) ),
    inference(resolution,[status(thm)],[c_18,c_865])).

tff(c_921,plain,(
    ! [B_16,A_15] :
      ( v1_relat_1(k7_relat_1(B_16,A_15))
      | ~ v1_relat_1(B_16) ) ),
    inference(resolution,[status(thm)],[c_28,c_899])).

tff(c_1678,plain,(
    ! [C_250,A_251,B_252] :
      ( m1_subset_1(C_250,k1_zfmisc_1(k2_zfmisc_1(A_251,B_252)))
      | ~ r1_tarski(k2_relat_1(C_250),B_252)
      | ~ r1_tarski(k1_relat_1(C_250),A_251)
      | ~ v1_relat_1(C_250) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_714,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( v1_funct_1(k2_partfun1(A_130,B_131,C_132,D_133))
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131)))
      | ~ v1_funct_1(C_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_719,plain,(
    ! [D_133] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_133))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_66,c_714])).

tff(c_727,plain,(
    ! [D_133] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_133)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_719])).

tff(c_60,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_146])).

tff(c_216,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_751,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_727,c_216])).

tff(c_752,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_796,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_1593,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1590,c_796])).

tff(c_1710,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1678,c_1593])).

tff(c_2115,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1710])).

tff(c_2118,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_921,c_2115])).

tff(c_2122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_2118])).

tff(c_2123,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1710])).

tff(c_2662,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2123])).

tff(c_2665,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_2662])).

tff(c_2669,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2279,c_2275,c_2665])).

tff(c_2670,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_2123])).

tff(c_2788,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1818,c_2670])).

tff(c_2794,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_6,c_2788])).

tff(c_2795,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_4098,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_2795])).

tff(c_2796,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_3474,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2796,c_3457])).

tff(c_4091,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_4088,c_3474])).

tff(c_4097,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4088,c_2796])).

tff(c_4359,plain,(
    ! [B_514,C_515,A_516] :
      ( k1_xboole_0 = B_514
      | v1_funct_2(C_515,A_516,B_514)
      | k1_relset_1(A_516,B_514,C_515) != A_516
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(A_516,B_514))) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_4362,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4097,c_4359])).

tff(c_4380,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4091,c_4362])).

tff(c_4381,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4098,c_77,c_4380])).

tff(c_4391,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_4224,c_4381])).

tff(c_4395,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4391])).

tff(c_4396,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4409,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4396,c_14])).

tff(c_4397,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_4402,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4397])).

tff(c_4408,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4402,c_66])).

tff(c_4410,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4409,c_4408])).

tff(c_4623,plain,(
    ! [A_543,B_544] :
      ( r1_tarski(A_543,B_544)
      | ~ m1_subset_1(A_543,k1_zfmisc_1(B_544)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4631,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4410,c_4623])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4434,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | ~ r1_tarski(A_3,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4396,c_8])).

tff(c_4646,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4631,c_4434])).

tff(c_4403,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4402,c_68])).

tff(c_4655,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_4403])).

tff(c_4461,plain,(
    ! [A_522,B_523] :
      ( r1_tarski(A_522,B_523)
      | ~ m1_subset_1(A_522,k1_zfmisc_1(B_523)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4465,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4410,c_4461])).

tff(c_4469,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4465,c_4434])).

tff(c_4446,plain,(
    ! [B_520,A_521] :
      ( r1_tarski(k7_relat_1(B_520,A_521),B_520)
      | ~ v1_relat_1(B_520) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4451,plain,(
    ! [A_521] :
      ( k7_relat_1('#skF_1',A_521) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4446,c_4434])).

tff(c_4458,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4451])).

tff(c_4472,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4469,c_4458])).

tff(c_4475,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4469,c_4410])).

tff(c_4477,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4469,c_4469,c_4409])).

tff(c_4573,plain,(
    ! [C_534,A_535,B_536] :
      ( v1_relat_1(C_534)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_535,B_536))) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4596,plain,(
    ! [C_539] :
      ( v1_relat_1(C_539)
      | ~ m1_subset_1(C_539,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4477,c_4573])).

tff(c_4599,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4475,c_4596])).

tff(c_4607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4472,c_4599])).

tff(c_4609,plain,(
    v1_relat_1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4451])).

tff(c_4632,plain,(
    ! [B_545,A_546] :
      ( v1_relat_1(B_545)
      | ~ m1_subset_1(B_545,k1_zfmisc_1(A_546))
      | ~ v1_relat_1(A_546) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4638,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4410,c_4632])).

tff(c_4642,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4609,c_4638])).

tff(c_4608,plain,(
    ! [A_521] : k7_relat_1('#skF_1',A_521) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_4451])).

tff(c_4648,plain,(
    ! [A_521] : k7_relat_1('#skF_4',A_521) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_4608])).

tff(c_8504,plain,(
    ! [B_1020,A_1021] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_1020,A_1021)),A_1021)
      | ~ v1_relat_1(B_1020) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8524,plain,(
    ! [A_521] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_521)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_8504])).

tff(c_8532,plain,(
    ! [A_1022] : r1_tarski(k1_relat_1('#skF_4'),A_1022) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_8524])).

tff(c_4651,plain,(
    ! [A_3] :
      ( A_3 = '#skF_4'
      | ~ r1_tarski(A_3,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_4434])).

tff(c_8554,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8532,c_4651])).

tff(c_8531,plain,(
    ! [A_521] : r1_tarski(k1_relat_1('#skF_4'),A_521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_8524])).

tff(c_8556,plain,(
    ! [A_521] : r1_tarski('#skF_4',A_521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8554,c_8531])).

tff(c_6407,plain,(
    ! [B_762,A_763] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_762,A_763)),A_763)
      | ~ v1_relat_1(B_762) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_6427,plain,(
    ! [A_521] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_521)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4648,c_6407])).

tff(c_6435,plain,(
    ! [A_764] : r1_tarski(k1_relat_1('#skF_4'),A_764) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_6427])).

tff(c_6457,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6435,c_4651])).

tff(c_6434,plain,(
    ! [A_521] : r1_tarski(k1_relat_1('#skF_4'),A_521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4642,c_6427])).

tff(c_6465,plain,(
    ! [A_521] : r1_tarski('#skF_4',A_521) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6457,c_6434])).

tff(c_7256,plain,(
    ! [A_866,B_867,C_868,D_869] :
      ( k2_partfun1(A_866,B_867,C_868,D_869) = k7_relat_1(C_868,D_869)
      | ~ m1_subset_1(C_868,k1_zfmisc_1(k2_zfmisc_1(A_866,B_867)))
      | ~ v1_funct_1(C_868) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_8442,plain,(
    ! [A_1011,B_1012,A_1013,D_1014] :
      ( k2_partfun1(A_1011,B_1012,A_1013,D_1014) = k7_relat_1(A_1013,D_1014)
      | ~ v1_funct_1(A_1013)
      | ~ r1_tarski(A_1013,k2_zfmisc_1(A_1011,B_1012)) ) ),
    inference(resolution,[status(thm)],[c_18,c_7256])).

tff(c_8448,plain,(
    ! [A_1011,B_1012,D_1014] :
      ( k2_partfun1(A_1011,B_1012,'#skF_4',D_1014) = k7_relat_1('#skF_4',D_1014)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6465,c_8442])).

tff(c_8465,plain,(
    ! [A_1011,B_1012,D_1014] : k2_partfun1(A_1011,B_1012,'#skF_4',D_1014) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4648,c_8448])).

tff(c_4654,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_4409])).

tff(c_4656,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4402])).

tff(c_4435,plain,(
    ! [A_519] :
      ( A_519 = '#skF_1'
      | ~ r1_tarski(A_519,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4396,c_4396,c_8])).

tff(c_4445,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_64,c_4435])).

tff(c_4650,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4445])).

tff(c_4652,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4410])).

tff(c_5436,plain,(
    ! [A_645,B_646,C_647,D_648] :
      ( v1_funct_1(k2_partfun1(A_645,B_646,C_647,D_648))
      | ~ m1_subset_1(C_647,k1_zfmisc_1(k2_zfmisc_1(A_645,B_646)))
      | ~ v1_funct_1(C_647) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_6224,plain,(
    ! [B_737,C_738,D_739] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_737,C_738,D_739))
      | ~ m1_subset_1(C_738,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_738) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4654,c_5436])).

tff(c_6226,plain,(
    ! [B_737,D_739] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_737,'#skF_4',D_739))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4652,c_6224])).

tff(c_6232,plain,(
    ! [B_737,D_739] : v1_funct_1(k2_partfun1('#skF_4',B_737,'#skF_4',D_739)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6226])).

tff(c_4664,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4646,c_4646,c_4646,c_60])).

tff(c_4665,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_4664])).

tff(c_4733,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4656,c_4650,c_4665])).

tff(c_6236,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6232,c_4733])).

tff(c_6237,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_4664])).

tff(c_6383,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4654,c_4656,c_4656,c_4650,c_4650,c_4656,c_4656,c_4650,c_4650,c_6237])).

tff(c_6384,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_6383])).

tff(c_6502,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_6384])).

tff(c_8473,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8465,c_6502])).

tff(c_8479,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8473])).

tff(c_8481,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_6383])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8635,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_8481,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8641,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_8635,c_2])).

tff(c_8652,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8556,c_8641])).

tff(c_8480,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_6383])).

tff(c_8660,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8652,c_8480])).

tff(c_8667,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4655,c_8660])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:57:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.08/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.51  
% 7.41/2.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.41/2.51  
% 7.41/2.51  %Foreground sorts:
% 7.41/2.51  
% 7.41/2.51  
% 7.41/2.51  %Background operators:
% 7.41/2.51  
% 7.41/2.51  
% 7.41/2.51  %Foreground operators:
% 7.41/2.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.41/2.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.41/2.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.41/2.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.41/2.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.41/2.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.41/2.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.41/2.51  tff('#skF_2', type, '#skF_2': $i).
% 7.41/2.51  tff('#skF_3', type, '#skF_3': $i).
% 7.41/2.51  tff('#skF_1', type, '#skF_1': $i).
% 7.41/2.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 7.41/2.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 7.41/2.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.41/2.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.41/2.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.41/2.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.41/2.51  tff('#skF_4', type, '#skF_4': $i).
% 7.41/2.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.41/2.51  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 7.41/2.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 7.41/2.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.41/2.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.41/2.51  
% 7.41/2.55  tff(f_146, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 7.41/2.55  tff(f_76, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.41/2.55  tff(f_86, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.41/2.55  tff(f_112, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.41/2.55  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 7.41/2.55  tff(f_126, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 7.41/2.55  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.41/2.55  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.41/2.55  tff(f_120, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 7.41/2.55  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 7.41/2.55  tff(f_82, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 7.41/2.55  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 7.41/2.55  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 7.41/2.55  tff(f_94, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 7.41/2.55  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.41/2.55  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.41/2.55  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 7.41/2.55  tff(c_64, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_173, plain, (![C_58, A_59, B_60]: (v1_relat_1(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.41/2.55  tff(c_186, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_173])).
% 7.41/2.55  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_77, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 7.41/2.55  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_3457, plain, (![A_429, B_430, C_431]: (k1_relset_1(A_429, B_430, C_431)=k1_relat_1(C_431) | ~m1_subset_1(C_431, k1_zfmisc_1(k2_zfmisc_1(A_429, B_430))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.41/2.55  tff(c_3476, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_3457])).
% 7.41/2.55  tff(c_4182, plain, (![B_509, A_510, C_511]: (k1_xboole_0=B_509 | k1_relset_1(A_510, B_509, C_511)=A_510 | ~v1_funct_2(C_511, A_510, B_509) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_510, B_509))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.41/2.55  tff(c_4195, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_4182])).
% 7.41/2.55  tff(c_4208, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3476, c_4195])).
% 7.41/2.55  tff(c_4209, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_4208])).
% 7.41/2.55  tff(c_30, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.41/2.55  tff(c_4218, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4209, c_30])).
% 7.41/2.55  tff(c_4224, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_4218])).
% 7.41/2.55  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_4067, plain, (![A_503, B_504, C_505, D_506]: (k2_partfun1(A_503, B_504, C_505, D_506)=k7_relat_1(C_505, D_506) | ~m1_subset_1(C_505, k1_zfmisc_1(k2_zfmisc_1(A_503, B_504))) | ~v1_funct_1(C_505))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.41/2.55  tff(c_4076, plain, (![D_506]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_506)=k7_relat_1('#skF_4', D_506) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_4067])).
% 7.41/2.55  tff(c_4088, plain, (![D_506]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_506)=k7_relat_1('#skF_4', D_506))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4076])).
% 7.41/2.55  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.55  tff(c_1352, plain, (![A_200, B_201, C_202]: (k1_relset_1(A_200, B_201, C_202)=k1_relat_1(C_202) | ~m1_subset_1(C_202, k1_zfmisc_1(k2_zfmisc_1(A_200, B_201))))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.41/2.55  tff(c_1367, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_1352])).
% 7.41/2.55  tff(c_1781, plain, (![B_261, A_262, C_263]: (k1_xboole_0=B_261 | k1_relset_1(A_262, B_261, C_263)=A_262 | ~v1_funct_2(C_263, A_262, B_261) | ~m1_subset_1(C_263, k1_zfmisc_1(k2_zfmisc_1(A_262, B_261))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.41/2.55  tff(c_1791, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_1781])).
% 7.41/2.55  tff(c_1802, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1367, c_1791])).
% 7.41/2.55  tff(c_1803, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_77, c_1802])).
% 7.41/2.55  tff(c_1812, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1803, c_30])).
% 7.41/2.55  tff(c_1818, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_186, c_1812])).
% 7.41/2.55  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.55  tff(c_797, plain, (![A_138, A_139, B_140]: (v1_relat_1(A_138) | ~r1_tarski(A_138, k2_zfmisc_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_18, c_173])).
% 7.41/2.55  tff(c_827, plain, (![A_139, B_140]: (v1_relat_1(k2_zfmisc_1(A_139, B_140)))), inference(resolution, [status(thm)], [c_6, c_797])).
% 7.41/2.55  tff(c_1577, plain, (![A_233, B_234, C_235, D_236]: (k2_partfun1(A_233, B_234, C_235, D_236)=k7_relat_1(C_235, D_236) | ~m1_subset_1(C_235, k1_zfmisc_1(k2_zfmisc_1(A_233, B_234))) | ~v1_funct_1(C_235))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.41/2.55  tff(c_1582, plain, (![D_236]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_236)=k7_relat_1('#skF_4', D_236) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_1577])).
% 7.41/2.55  tff(c_1590, plain, (![D_236]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_236)=k7_relat_1('#skF_4', D_236))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_1582])).
% 7.41/2.55  tff(c_2179, plain, (![A_294, B_295, C_296, D_297]: (m1_subset_1(k2_partfun1(A_294, B_295, C_296, D_297), k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~m1_subset_1(C_296, k1_zfmisc_1(k2_zfmisc_1(A_294, B_295))) | ~v1_funct_1(C_296))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.41/2.55  tff(c_2210, plain, (![D_236]: (m1_subset_1(k7_relat_1('#skF_4', D_236), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1590, c_2179])).
% 7.41/2.55  tff(c_2233, plain, (![D_298]: (m1_subset_1(k7_relat_1('#skF_4', D_298), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_66, c_2210])).
% 7.41/2.55  tff(c_20, plain, (![B_10, A_8]: (v1_relat_1(B_10) | ~m1_subset_1(B_10, k1_zfmisc_1(A_8)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.41/2.55  tff(c_2255, plain, (![D_298]: (v1_relat_1(k7_relat_1('#skF_4', D_298)) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_2233, c_20])).
% 7.41/2.55  tff(c_2279, plain, (![D_298]: (v1_relat_1(k7_relat_1('#skF_4', D_298)))), inference(demodulation, [status(thm), theory('equality')], [c_827, c_2255])).
% 7.41/2.55  tff(c_34, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.41/2.55  tff(c_2275, plain, (![D_298]: (v5_relat_1(k7_relat_1('#skF_4', D_298), '#skF_2'))), inference(resolution, [status(thm)], [c_2233, c_34])).
% 7.41/2.55  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(B_12), A_11) | ~v5_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.41/2.55  tff(c_28, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.41/2.55  tff(c_865, plain, (![B_145, A_146]: (v1_relat_1(B_145) | ~m1_subset_1(B_145, k1_zfmisc_1(A_146)) | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.41/2.55  tff(c_899, plain, (![A_149, B_150]: (v1_relat_1(A_149) | ~v1_relat_1(B_150) | ~r1_tarski(A_149, B_150))), inference(resolution, [status(thm)], [c_18, c_865])).
% 7.41/2.55  tff(c_921, plain, (![B_16, A_15]: (v1_relat_1(k7_relat_1(B_16, A_15)) | ~v1_relat_1(B_16))), inference(resolution, [status(thm)], [c_28, c_899])).
% 7.41/2.55  tff(c_1678, plain, (![C_250, A_251, B_252]: (m1_subset_1(C_250, k1_zfmisc_1(k2_zfmisc_1(A_251, B_252))) | ~r1_tarski(k2_relat_1(C_250), B_252) | ~r1_tarski(k1_relat_1(C_250), A_251) | ~v1_relat_1(C_250))), inference(cnfTransformation, [status(thm)], [f_94])).
% 7.41/2.55  tff(c_714, plain, (![A_130, B_131, C_132, D_133]: (v1_funct_1(k2_partfun1(A_130, B_131, C_132, D_133)) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))) | ~v1_funct_1(C_132))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.41/2.55  tff(c_719, plain, (![D_133]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_133)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_66, c_714])).
% 7.41/2.55  tff(c_727, plain, (![D_133]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_133)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_719])).
% 7.41/2.55  tff(c_60, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_146])).
% 7.41/2.55  tff(c_216, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_60])).
% 7.41/2.55  tff(c_751, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_727, c_216])).
% 7.41/2.55  tff(c_752, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_60])).
% 7.41/2.55  tff(c_796, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_752])).
% 7.41/2.55  tff(c_1593, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1590, c_796])).
% 7.41/2.55  tff(c_1710, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1678, c_1593])).
% 7.41/2.55  tff(c_2115, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1710])).
% 7.41/2.55  tff(c_2118, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_921, c_2115])).
% 7.41/2.55  tff(c_2122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_2118])).
% 7.41/2.55  tff(c_2123, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1710])).
% 7.41/2.55  tff(c_2662, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_2123])).
% 7.41/2.55  tff(c_2665, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_2662])).
% 7.41/2.55  tff(c_2669, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2279, c_2275, c_2665])).
% 7.41/2.55  tff(c_2670, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_2123])).
% 7.41/2.55  tff(c_2788, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1818, c_2670])).
% 7.41/2.55  tff(c_2794, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_6, c_2788])).
% 7.41/2.55  tff(c_2795, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_752])).
% 7.41/2.55  tff(c_4098, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_2795])).
% 7.41/2.55  tff(c_2796, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_752])).
% 7.41/2.55  tff(c_3474, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2796, c_3457])).
% 7.41/2.55  tff(c_4091, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_4088, c_3474])).
% 7.41/2.55  tff(c_4097, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4088, c_2796])).
% 7.41/2.55  tff(c_4359, plain, (![B_514, C_515, A_516]: (k1_xboole_0=B_514 | v1_funct_2(C_515, A_516, B_514) | k1_relset_1(A_516, B_514, C_515)!=A_516 | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(A_516, B_514))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 7.41/2.55  tff(c_4362, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_4097, c_4359])).
% 7.41/2.55  tff(c_4380, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4091, c_4362])).
% 7.41/2.55  tff(c_4381, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4098, c_77, c_4380])).
% 7.41/2.55  tff(c_4391, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_4224, c_4381])).
% 7.41/2.55  tff(c_4395, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_4391])).
% 7.41/2.55  tff(c_4396, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 7.41/2.55  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.41/2.55  tff(c_4409, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4396, c_14])).
% 7.41/2.55  tff(c_4397, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 7.41/2.55  tff(c_4402, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4397])).
% 7.41/2.55  tff(c_4408, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_4402, c_66])).
% 7.41/2.55  tff(c_4410, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4409, c_4408])).
% 7.41/2.55  tff(c_4623, plain, (![A_543, B_544]: (r1_tarski(A_543, B_544) | ~m1_subset_1(A_543, k1_zfmisc_1(B_544)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.55  tff(c_4631, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4410, c_4623])).
% 7.41/2.55  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.41/2.55  tff(c_4434, plain, (![A_3]: (A_3='#skF_1' | ~r1_tarski(A_3, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4396, c_8])).
% 7.41/2.55  tff(c_4646, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4631, c_4434])).
% 7.41/2.55  tff(c_4403, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_4402, c_68])).
% 7.41/2.55  tff(c_4655, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_4403])).
% 7.41/2.55  tff(c_4461, plain, (![A_522, B_523]: (r1_tarski(A_522, B_523) | ~m1_subset_1(A_522, k1_zfmisc_1(B_523)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.55  tff(c_4465, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4410, c_4461])).
% 7.41/2.55  tff(c_4469, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4465, c_4434])).
% 7.41/2.55  tff(c_4446, plain, (![B_520, A_521]: (r1_tarski(k7_relat_1(B_520, A_521), B_520) | ~v1_relat_1(B_520))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.41/2.55  tff(c_4451, plain, (![A_521]: (k7_relat_1('#skF_1', A_521)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4446, c_4434])).
% 7.41/2.55  tff(c_4458, plain, (~v1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_4451])).
% 7.41/2.55  tff(c_4472, plain, (~v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4469, c_4458])).
% 7.41/2.55  tff(c_4475, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4469, c_4410])).
% 7.41/2.55  tff(c_4477, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4469, c_4469, c_4409])).
% 7.41/2.55  tff(c_4573, plain, (![C_534, A_535, B_536]: (v1_relat_1(C_534) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_535, B_536))))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.41/2.55  tff(c_4596, plain, (![C_539]: (v1_relat_1(C_539) | ~m1_subset_1(C_539, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_4477, c_4573])).
% 7.41/2.55  tff(c_4599, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_4475, c_4596])).
% 7.41/2.55  tff(c_4607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4472, c_4599])).
% 7.41/2.55  tff(c_4609, plain, (v1_relat_1('#skF_1')), inference(splitRight, [status(thm)], [c_4451])).
% 7.41/2.55  tff(c_4632, plain, (![B_545, A_546]: (v1_relat_1(B_545) | ~m1_subset_1(B_545, k1_zfmisc_1(A_546)) | ~v1_relat_1(A_546))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.41/2.55  tff(c_4638, plain, (v1_relat_1('#skF_4') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4410, c_4632])).
% 7.41/2.55  tff(c_4642, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4609, c_4638])).
% 7.41/2.55  tff(c_4608, plain, (![A_521]: (k7_relat_1('#skF_1', A_521)='#skF_1')), inference(splitRight, [status(thm)], [c_4451])).
% 7.41/2.55  tff(c_4648, plain, (![A_521]: (k7_relat_1('#skF_4', A_521)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_4608])).
% 7.41/2.55  tff(c_8504, plain, (![B_1020, A_1021]: (r1_tarski(k1_relat_1(k7_relat_1(B_1020, A_1021)), A_1021) | ~v1_relat_1(B_1020))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.41/2.55  tff(c_8524, plain, (![A_521]: (r1_tarski(k1_relat_1('#skF_4'), A_521) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4648, c_8504])).
% 7.41/2.55  tff(c_8532, plain, (![A_1022]: (r1_tarski(k1_relat_1('#skF_4'), A_1022))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_8524])).
% 7.41/2.55  tff(c_4651, plain, (![A_3]: (A_3='#skF_4' | ~r1_tarski(A_3, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_4434])).
% 7.41/2.55  tff(c_8554, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8532, c_4651])).
% 7.41/2.55  tff(c_8531, plain, (![A_521]: (r1_tarski(k1_relat_1('#skF_4'), A_521))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_8524])).
% 7.41/2.55  tff(c_8556, plain, (![A_521]: (r1_tarski('#skF_4', A_521))), inference(demodulation, [status(thm), theory('equality')], [c_8554, c_8531])).
% 7.41/2.55  tff(c_6407, plain, (![B_762, A_763]: (r1_tarski(k1_relat_1(k7_relat_1(B_762, A_763)), A_763) | ~v1_relat_1(B_762))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.41/2.55  tff(c_6427, plain, (![A_521]: (r1_tarski(k1_relat_1('#skF_4'), A_521) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4648, c_6407])).
% 7.41/2.55  tff(c_6435, plain, (![A_764]: (r1_tarski(k1_relat_1('#skF_4'), A_764))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_6427])).
% 7.41/2.55  tff(c_6457, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6435, c_4651])).
% 7.41/2.55  tff(c_6434, plain, (![A_521]: (r1_tarski(k1_relat_1('#skF_4'), A_521))), inference(demodulation, [status(thm), theory('equality')], [c_4642, c_6427])).
% 7.41/2.55  tff(c_6465, plain, (![A_521]: (r1_tarski('#skF_4', A_521))), inference(demodulation, [status(thm), theory('equality')], [c_6457, c_6434])).
% 7.41/2.55  tff(c_7256, plain, (![A_866, B_867, C_868, D_869]: (k2_partfun1(A_866, B_867, C_868, D_869)=k7_relat_1(C_868, D_869) | ~m1_subset_1(C_868, k1_zfmisc_1(k2_zfmisc_1(A_866, B_867))) | ~v1_funct_1(C_868))), inference(cnfTransformation, [status(thm)], [f_126])).
% 7.41/2.55  tff(c_8442, plain, (![A_1011, B_1012, A_1013, D_1014]: (k2_partfun1(A_1011, B_1012, A_1013, D_1014)=k7_relat_1(A_1013, D_1014) | ~v1_funct_1(A_1013) | ~r1_tarski(A_1013, k2_zfmisc_1(A_1011, B_1012)))), inference(resolution, [status(thm)], [c_18, c_7256])).
% 7.41/2.55  tff(c_8448, plain, (![A_1011, B_1012, D_1014]: (k2_partfun1(A_1011, B_1012, '#skF_4', D_1014)=k7_relat_1('#skF_4', D_1014) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6465, c_8442])).
% 7.41/2.55  tff(c_8465, plain, (![A_1011, B_1012, D_1014]: (k2_partfun1(A_1011, B_1012, '#skF_4', D_1014)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_4648, c_8448])).
% 7.41/2.55  tff(c_4654, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_4409])).
% 7.41/2.55  tff(c_4656, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4402])).
% 7.41/2.55  tff(c_4435, plain, (![A_519]: (A_519='#skF_1' | ~r1_tarski(A_519, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4396, c_4396, c_8])).
% 7.41/2.55  tff(c_4445, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_64, c_4435])).
% 7.41/2.55  tff(c_4650, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4445])).
% 7.41/2.55  tff(c_4652, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4410])).
% 7.41/2.55  tff(c_5436, plain, (![A_645, B_646, C_647, D_648]: (v1_funct_1(k2_partfun1(A_645, B_646, C_647, D_648)) | ~m1_subset_1(C_647, k1_zfmisc_1(k2_zfmisc_1(A_645, B_646))) | ~v1_funct_1(C_647))), inference(cnfTransformation, [status(thm)], [f_120])).
% 7.41/2.55  tff(c_6224, plain, (![B_737, C_738, D_739]: (v1_funct_1(k2_partfun1('#skF_4', B_737, C_738, D_739)) | ~m1_subset_1(C_738, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_738))), inference(superposition, [status(thm), theory('equality')], [c_4654, c_5436])).
% 7.41/2.55  tff(c_6226, plain, (![B_737, D_739]: (v1_funct_1(k2_partfun1('#skF_4', B_737, '#skF_4', D_739)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4652, c_6224])).
% 7.41/2.55  tff(c_6232, plain, (![B_737, D_739]: (v1_funct_1(k2_partfun1('#skF_4', B_737, '#skF_4', D_739)))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6226])).
% 7.41/2.55  tff(c_4664, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4646, c_4646, c_4646, c_60])).
% 7.41/2.55  tff(c_4665, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_4664])).
% 7.41/2.55  tff(c_4733, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4656, c_4650, c_4665])).
% 7.41/2.55  tff(c_6236, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6232, c_4733])).
% 7.41/2.55  tff(c_6237, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_4664])).
% 7.41/2.55  tff(c_6383, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4654, c_4656, c_4656, c_4650, c_4650, c_4656, c_4656, c_4650, c_4650, c_6237])).
% 7.41/2.55  tff(c_6384, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_6383])).
% 7.41/2.55  tff(c_6502, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_18, c_6384])).
% 7.41/2.55  tff(c_8473, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8465, c_6502])).
% 7.41/2.55  tff(c_8479, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_8473])).
% 7.41/2.55  tff(c_8481, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_6383])).
% 7.41/2.55  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.41/2.55  tff(c_8635, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_8481, c_16])).
% 7.41/2.55  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.41/2.55  tff(c_8641, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_8635, c_2])).
% 7.41/2.55  tff(c_8652, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_8556, c_8641])).
% 7.41/2.55  tff(c_8480, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_6383])).
% 7.41/2.55  tff(c_8660, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8652, c_8480])).
% 7.41/2.55  tff(c_8667, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4655, c_8660])).
% 7.41/2.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.41/2.55  
% 7.41/2.55  Inference rules
% 7.41/2.55  ----------------------
% 7.41/2.55  #Ref     : 0
% 7.41/2.55  #Sup     : 1811
% 7.41/2.55  #Fact    : 0
% 7.41/2.55  #Define  : 0
% 7.41/2.55  #Split   : 27
% 7.41/2.55  #Chain   : 0
% 7.41/2.55  #Close   : 0
% 7.41/2.55  
% 7.41/2.55  Ordering : KBO
% 7.41/2.55  
% 7.41/2.55  Simplification rules
% 7.41/2.55  ----------------------
% 7.41/2.55  #Subsume      : 169
% 7.41/2.55  #Demod        : 1914
% 7.41/2.55  #Tautology    : 901
% 7.41/2.55  #SimpNegUnit  : 13
% 7.41/2.55  #BackRed      : 61
% 7.41/2.55  
% 7.41/2.55  #Partial instantiations: 0
% 7.41/2.55  #Strategies tried      : 1
% 7.41/2.55  
% 7.41/2.55  Timing (in seconds)
% 7.41/2.55  ----------------------
% 7.41/2.55  Preprocessing        : 0.34
% 7.41/2.55  Parsing              : 0.18
% 7.41/2.55  CNF conversion       : 0.02
% 7.41/2.55  Main loop            : 1.41
% 7.41/2.55  Inferencing          : 0.52
% 7.41/2.55  Reduction            : 0.48
% 7.41/2.55  Demodulation         : 0.35
% 7.41/2.55  BG Simplification    : 0.05
% 7.41/2.55  Subsumption          : 0.24
% 7.41/2.55  Abstraction          : 0.05
% 7.41/2.55  MUC search           : 0.00
% 7.41/2.55  Cooper               : 0.00
% 7.41/2.55  Total                : 1.83
% 7.41/2.55  Index Insertion      : 0.00
% 7.41/2.55  Index Deletion       : 0.00
% 7.41/2.55  Index Matching       : 0.00
% 7.41/2.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
