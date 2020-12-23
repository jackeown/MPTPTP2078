%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 6.45s
% Output     : CNFRefutation 6.45s
% Verified   : 
% Statistics : Number of formulae       :  176 (2080 expanded)
%              Number of leaves         :   39 ( 641 expanded)
%              Depth                    :   15
%              Number of atoms          :  270 (6438 expanded)
%              Number of equality atoms :   71 (2506 expanded)
%              Maximal formula depth    :   11 (   3 average)
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

tff(f_139,negated_conjecture,(
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

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_119,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_113,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_649,plain,(
    ! [C_124,A_125,B_126] :
      ( v1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_662,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_649])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2479,plain,(
    ! [A_338,B_339,C_340] :
      ( k1_relset_1(A_338,B_339,C_340) = k1_relat_1(C_340)
      | ~ m1_subset_1(C_340,k1_zfmisc_1(k2_zfmisc_1(A_338,B_339))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2498,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2479])).

tff(c_3154,plain,(
    ! [B_426,A_427,C_428] :
      ( k1_xboole_0 = B_426
      | k1_relset_1(A_427,B_426,C_428) = A_427
      | ~ v1_funct_2(C_428,A_427,B_426)
      | ~ m1_subset_1(C_428,k1_zfmisc_1(k2_zfmisc_1(A_427,B_426))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3167,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_3154])).

tff(c_3181,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_2498,c_3167])).

tff(c_3182,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_3181])).

tff(c_26,plain,(
    ! [B_17,A_16] :
      ( k1_relat_1(k7_relat_1(B_17,A_16)) = A_16
      | ~ r1_tarski(A_16,k1_relat_1(B_17))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_3188,plain,(
    ! [A_16] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_16)) = A_16
      | ~ r1_tarski(A_16,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3182,c_26])).

tff(c_3198,plain,(
    ! [A_429] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_429)) = A_429
      | ~ r1_tarski(A_429,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_3188])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_2835,plain,(
    ! [A_387,B_388,C_389,D_390] :
      ( k2_partfun1(A_387,B_388,C_389,D_390) = k7_relat_1(C_389,D_390)
      | ~ m1_subset_1(C_389,k1_zfmisc_1(k2_zfmisc_1(A_387,B_388)))
      | ~ v1_funct_1(C_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_2842,plain,(
    ! [D_390] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_390) = k7_relat_1('#skF_4',D_390)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_2835])).

tff(c_2853,plain,(
    ! [D_390] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_390) = k7_relat_1('#skF_4',D_390) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2842])).

tff(c_22,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1359,plain,(
    ! [A_223,B_224,C_225,D_226] :
      ( k2_partfun1(A_223,B_224,C_225,D_226) = k7_relat_1(C_225,D_226)
      | ~ m1_subset_1(C_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(C_225) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1364,plain,(
    ! [D_226] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_226) = k7_relat_1('#skF_4',D_226)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_1359])).

tff(c_1372,plain,(
    ! [D_226] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_226) = k7_relat_1('#skF_4',D_226) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1364])).

tff(c_1851,plain,(
    ! [A_270,B_271,C_272,D_273] :
      ( m1_subset_1(k2_partfun1(A_270,B_271,C_272,D_273),k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ m1_subset_1(C_272,k1_zfmisc_1(k2_zfmisc_1(A_270,B_271)))
      | ~ v1_funct_1(C_272) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1879,plain,(
    ! [D_226] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_226),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1372,c_1851])).

tff(c_1899,plain,(
    ! [D_274] : m1_subset_1(k7_relat_1('#skF_4',D_274),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_62,c_1879])).

tff(c_30,plain,(
    ! [C_23,B_22,A_21] :
      ( v5_relat_1(C_23,B_22)
      | ~ m1_subset_1(C_23,k1_zfmisc_1(k2_zfmisc_1(A_21,B_22))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1938,plain,(
    ! [D_274] : v5_relat_1(k7_relat_1('#skF_4',D_274),'#skF_2') ),
    inference(resolution,[status(thm)],[c_1899,c_30])).

tff(c_18,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1396,plain,(
    ! [C_230,A_231,B_232] :
      ( m1_subset_1(C_230,k1_zfmisc_1(k2_zfmisc_1(A_231,B_232)))
      | ~ r1_tarski(k2_relat_1(C_230),B_232)
      | ~ r1_tarski(k1_relat_1(C_230),A_231)
      | ~ v1_relat_1(C_230) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_630,plain,(
    ! [A_120,B_121,C_122,D_123] :
      ( v1_funct_1(k2_partfun1(A_120,B_121,C_122,D_123))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121)))
      | ~ v1_funct_1(C_122) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_635,plain,(
    ! [D_123] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_123))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_630])).

tff(c_643,plain,(
    ! [D_123] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_123)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_635])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_153,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_646,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_153])).

tff(c_647,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_699,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_647])).

tff(c_1375,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_699])).

tff(c_1425,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_1396,c_1375])).

tff(c_1488,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1425])).

tff(c_1491,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_1488])).

tff(c_1495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_1491])).

tff(c_1497,plain,(
    v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1425])).

tff(c_16,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1496,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1425])).

tff(c_1651,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1496])).

tff(c_1654,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_16,c_1651])).

tff(c_1657,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1497,c_1654])).

tff(c_1948,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1938,c_1657])).

tff(c_1949,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_1496])).

tff(c_2022,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1949])).

tff(c_2028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_662,c_2022])).

tff(c_2029,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_2862,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_2029])).

tff(c_2030,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_647])).

tff(c_2496,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_2030,c_2479])).

tff(c_2856,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_2853,c_2496])).

tff(c_2861,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2853,c_2030])).

tff(c_3084,plain,(
    ! [B_409,C_410,A_411] :
      ( k1_xboole_0 = B_409
      | v1_funct_2(C_410,A_411,B_409)
      | k1_relset_1(A_411,B_409,C_410) != A_411
      | ~ m1_subset_1(C_410,k1_zfmisc_1(k2_zfmisc_1(A_411,B_409))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_3090,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_2861,c_3084])).

tff(c_3106,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_3090])).

tff(c_3107,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2862,c_71,c_3106])).

tff(c_3204,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3198,c_3107])).

tff(c_3250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_3204])).

tff(c_3251,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3272,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_3251,c_6])).

tff(c_3252,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_3257,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_3252])).

tff(c_3258,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_62])).

tff(c_4452,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3258])).

tff(c_4454,plain,(
    ! [A_597,B_598] :
      ( r1_tarski(A_597,B_598)
      | ~ m1_subset_1(A_597,k1_zfmisc_1(B_598)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4458,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_4452,c_4454])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_3294,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ r1_tarski(A_1,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_3251,c_2])).

tff(c_4462,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4458,c_3294])).

tff(c_3259,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_64])).

tff(c_6502,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_3259])).

tff(c_3288,plain,(
    ! [A_432,B_433] : v1_relat_1(k2_zfmisc_1(A_432,B_433)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3290,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3272,c_3288])).

tff(c_4471,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_3290])).

tff(c_24,plain,(
    ! [B_15,A_14] :
      ( r1_tarski(k7_relat_1(B_15,A_14),B_15)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4528,plain,(
    ! [A_603] :
      ( A_603 = '#skF_4'
      | ~ r1_tarski(A_603,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_3294])).

tff(c_4535,plain,(
    ! [A_14] :
      ( k7_relat_1('#skF_4',A_14) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_4528])).

tff(c_4540,plain,(
    ! [A_14] : k7_relat_1('#skF_4',A_14) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_4535])).

tff(c_4563,plain,(
    ! [B_607,A_608] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_607,A_608)),A_608)
      | ~ v1_relat_1(B_607) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4570,plain,(
    ! [A_14] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_14)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4540,c_4563])).

tff(c_4574,plain,(
    ! [A_609] : r1_tarski(k1_relat_1('#skF_4'),A_609) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_4570])).

tff(c_4470,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_3294])).

tff(c_4579,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4574,c_4470])).

tff(c_4573,plain,(
    ! [A_14] : r1_tarski(k1_relat_1('#skF_4'),A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4471,c_4570])).

tff(c_4580,plain,(
    ! [A_14] : r1_tarski('#skF_4',A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4579,c_4573])).

tff(c_4467,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4452])).

tff(c_4473,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_3272])).

tff(c_5520,plain,(
    ! [A_753,B_754,C_755,D_756] :
      ( k2_partfun1(A_753,B_754,C_755,D_756) = k7_relat_1(C_755,D_756)
      | ~ m1_subset_1(C_755,k1_zfmisc_1(k2_zfmisc_1(A_753,B_754)))
      | ~ v1_funct_1(C_755) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6478,plain,(
    ! [A_860,C_861,D_862] :
      ( k2_partfun1(A_860,'#skF_4',C_861,D_862) = k7_relat_1(C_861,D_862)
      | ~ m1_subset_1(C_861,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_861) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4473,c_5520])).

tff(c_6483,plain,(
    ! [A_860,D_862] :
      ( k2_partfun1(A_860,'#skF_4','#skF_4',D_862) = k7_relat_1('#skF_4',D_862)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4467,c_6478])).

tff(c_6487,plain,(
    ! [A_860,D_862] : k2_partfun1(A_860,'#skF_4','#skF_4',D_862) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4540,c_6483])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3295,plain,(
    ! [A_434] :
      ( A_434 = '#skF_1'
      | ~ r1_tarski(A_434,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_3251,c_2])).

tff(c_3299,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_3295])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3264,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3251,c_3251,c_8])).

tff(c_3313,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3264,c_3258])).

tff(c_3341,plain,(
    ! [A_442,B_443] :
      ( r1_tarski(A_442,B_443)
      | ~ m1_subset_1(A_442,k1_zfmisc_1(B_443)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3349,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3313,c_3341])).

tff(c_3353,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3349,c_3294])).

tff(c_3357,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_3313])).

tff(c_3364,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_4',B_3) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_3353,c_3264])).

tff(c_3937,plain,(
    ! [A_523,B_524,C_525,D_526] :
      ( v1_funct_1(k2_partfun1(A_523,B_524,C_525,D_526))
      | ~ m1_subset_1(C_525,k1_zfmisc_1(k2_zfmisc_1(A_523,B_524)))
      | ~ v1_funct_1(C_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_4426,plain,(
    ! [B_592,C_593,D_594] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_592,C_593,D_594))
      | ~ m1_subset_1(C_593,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_593) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3364,c_3937])).

tff(c_4428,plain,(
    ! [B_592,D_594] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_592,'#skF_4',D_594))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3357,c_4426])).

tff(c_4434,plain,(
    ! [B_592,D_594] : v1_funct_1(k2_partfun1('#skF_4',B_592,'#skF_4',D_594)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4428])).

tff(c_3300,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3257,c_3257,c_3257,c_3272,c_3257,c_3257,c_56])).

tff(c_3301,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3300])).

tff(c_3314,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3299,c_3301])).

tff(c_3356,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3353,c_3353,c_3353,c_3314])).

tff(c_4438,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4434,c_3356])).

tff(c_4439,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_3300])).

tff(c_4463,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3299,c_3299,c_3299,c_4439])).

tff(c_4464,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_4463])).

tff(c_4585,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_4462,c_4462,c_4464])).

tff(c_4589,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_4585])).

tff(c_6488,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6487,c_4589])).

tff(c_6492,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4580,c_6488])).

tff(c_6494,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_6696,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_4462,c_4462,c_6494])).

tff(c_10,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_6704,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6696,c_10])).

tff(c_6500,plain,(
    ! [A_1] :
      ( A_1 = '#skF_4'
      | ~ r1_tarski(A_1,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_3294])).

tff(c_6772,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_6704,c_6500])).

tff(c_6493,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(splitRight,[status(thm)],[c_4463])).

tff(c_6593,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4462,c_4462,c_4462,c_4462,c_4462,c_6493])).

tff(c_6776,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6772,c_6593])).

tff(c_6783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6502,c_6776])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.45/2.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.33  
% 6.45/2.33  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.33  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.45/2.33  
% 6.45/2.33  %Foreground sorts:
% 6.45/2.33  
% 6.45/2.33  
% 6.45/2.33  %Background operators:
% 6.45/2.33  
% 6.45/2.33  
% 6.45/2.33  %Foreground operators:
% 6.45/2.33  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.45/2.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.45/2.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.45/2.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.45/2.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.45/2.33  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.45/2.33  tff('#skF_2', type, '#skF_2': $i).
% 6.45/2.33  tff('#skF_3', type, '#skF_3': $i).
% 6.45/2.33  tff('#skF_1', type, '#skF_1': $i).
% 6.45/2.33  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.45/2.33  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.45/2.33  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.45/2.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.45/2.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.45/2.33  tff('#skF_4', type, '#skF_4': $i).
% 6.45/2.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.45/2.33  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.45/2.33  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.45/2.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.45/2.33  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.45/2.33  
% 6.45/2.35  tff(f_139, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.45/2.35  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.45/2.35  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.45/2.35  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.45/2.35  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.45/2.35  tff(f_119, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.45/2.35  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 6.45/2.35  tff(f_113, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.45/2.35  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 6.45/2.35  tff(f_49, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 6.45/2.35  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.45/2.35  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 6.45/2.35  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.45/2.35  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.45/2.35  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.45/2.35  tff(f_51, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.45/2.35  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.45/2.35  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_649, plain, (![C_124, A_125, B_126]: (v1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.45/2.35  tff(c_662, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_649])).
% 6.45/2.35  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 6.45/2.35  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_2479, plain, (![A_338, B_339, C_340]: (k1_relset_1(A_338, B_339, C_340)=k1_relat_1(C_340) | ~m1_subset_1(C_340, k1_zfmisc_1(k2_zfmisc_1(A_338, B_339))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.45/2.35  tff(c_2498, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2479])).
% 6.45/2.35  tff(c_3154, plain, (![B_426, A_427, C_428]: (k1_xboole_0=B_426 | k1_relset_1(A_427, B_426, C_428)=A_427 | ~v1_funct_2(C_428, A_427, B_426) | ~m1_subset_1(C_428, k1_zfmisc_1(k2_zfmisc_1(A_427, B_426))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.45/2.35  tff(c_3167, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_3154])).
% 6.45/2.35  tff(c_3181, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_2498, c_3167])).
% 6.45/2.35  tff(c_3182, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_3181])).
% 6.45/2.35  tff(c_26, plain, (![B_17, A_16]: (k1_relat_1(k7_relat_1(B_17, A_16))=A_16 | ~r1_tarski(A_16, k1_relat_1(B_17)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.45/2.35  tff(c_3188, plain, (![A_16]: (k1_relat_1(k7_relat_1('#skF_4', A_16))=A_16 | ~r1_tarski(A_16, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3182, c_26])).
% 6.45/2.35  tff(c_3198, plain, (![A_429]: (k1_relat_1(k7_relat_1('#skF_4', A_429))=A_429 | ~r1_tarski(A_429, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_662, c_3188])).
% 6.45/2.35  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_2835, plain, (![A_387, B_388, C_389, D_390]: (k2_partfun1(A_387, B_388, C_389, D_390)=k7_relat_1(C_389, D_390) | ~m1_subset_1(C_389, k1_zfmisc_1(k2_zfmisc_1(A_387, B_388))) | ~v1_funct_1(C_389))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.45/2.35  tff(c_2842, plain, (![D_390]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_390)=k7_relat_1('#skF_4', D_390) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_2835])).
% 6.45/2.35  tff(c_2853, plain, (![D_390]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_390)=k7_relat_1('#skF_4', D_390))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2842])).
% 6.45/2.35  tff(c_22, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.35  tff(c_1359, plain, (![A_223, B_224, C_225, D_226]: (k2_partfun1(A_223, B_224, C_225, D_226)=k7_relat_1(C_225, D_226) | ~m1_subset_1(C_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(C_225))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.45/2.35  tff(c_1364, plain, (![D_226]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_226)=k7_relat_1('#skF_4', D_226) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_1359])).
% 6.45/2.35  tff(c_1372, plain, (![D_226]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_226)=k7_relat_1('#skF_4', D_226))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1364])).
% 6.45/2.35  tff(c_1851, plain, (![A_270, B_271, C_272, D_273]: (m1_subset_1(k2_partfun1(A_270, B_271, C_272, D_273), k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~m1_subset_1(C_272, k1_zfmisc_1(k2_zfmisc_1(A_270, B_271))) | ~v1_funct_1(C_272))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.45/2.35  tff(c_1879, plain, (![D_226]: (m1_subset_1(k7_relat_1('#skF_4', D_226), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1372, c_1851])).
% 6.45/2.35  tff(c_1899, plain, (![D_274]: (m1_subset_1(k7_relat_1('#skF_4', D_274), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_62, c_1879])).
% 6.45/2.35  tff(c_30, plain, (![C_23, B_22, A_21]: (v5_relat_1(C_23, B_22) | ~m1_subset_1(C_23, k1_zfmisc_1(k2_zfmisc_1(A_21, B_22))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.45/2.35  tff(c_1938, plain, (![D_274]: (v5_relat_1(k7_relat_1('#skF_4', D_274), '#skF_2'))), inference(resolution, [status(thm)], [c_1899, c_30])).
% 6.45/2.35  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.45/2.35  tff(c_1396, plain, (![C_230, A_231, B_232]: (m1_subset_1(C_230, k1_zfmisc_1(k2_zfmisc_1(A_231, B_232))) | ~r1_tarski(k2_relat_1(C_230), B_232) | ~r1_tarski(k1_relat_1(C_230), A_231) | ~v1_relat_1(C_230))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.45/2.35  tff(c_630, plain, (![A_120, B_121, C_122, D_123]: (v1_funct_1(k2_partfun1(A_120, B_121, C_122, D_123)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))) | ~v1_funct_1(C_122))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.45/2.35  tff(c_635, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_630])).
% 6.45/2.35  tff(c_643, plain, (![D_123]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_123)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_635])).
% 6.45/2.35  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 6.45/2.35  tff(c_153, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 6.45/2.35  tff(c_646, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_643, c_153])).
% 6.45/2.35  tff(c_647, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 6.45/2.35  tff(c_699, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_647])).
% 6.45/2.35  tff(c_1375, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_699])).
% 6.45/2.35  tff(c_1425, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_1396, c_1375])).
% 6.45/2.35  tff(c_1488, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1425])).
% 6.45/2.35  tff(c_1491, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_18, c_1488])).
% 6.45/2.35  tff(c_1495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_662, c_1491])).
% 6.45/2.35  tff(c_1497, plain, (v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(splitRight, [status(thm)], [c_1425])).
% 6.45/2.35  tff(c_16, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.45/2.35  tff(c_1496, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_1425])).
% 6.45/2.35  tff(c_1651, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitLeft, [status(thm)], [c_1496])).
% 6.45/2.35  tff(c_1654, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_16, c_1651])).
% 6.45/2.35  tff(c_1657, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1497, c_1654])).
% 6.45/2.35  tff(c_1948, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1938, c_1657])).
% 6.45/2.35  tff(c_1949, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitRight, [status(thm)], [c_1496])).
% 6.45/2.35  tff(c_2022, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_1949])).
% 6.45/2.35  tff(c_2028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_662, c_2022])).
% 6.45/2.35  tff(c_2029, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_647])).
% 6.45/2.35  tff(c_2862, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2853, c_2029])).
% 6.45/2.35  tff(c_2030, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_647])).
% 6.45/2.35  tff(c_2496, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_2030, c_2479])).
% 6.45/2.35  tff(c_2856, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2853, c_2853, c_2496])).
% 6.45/2.35  tff(c_2861, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2853, c_2030])).
% 6.45/2.35  tff(c_3084, plain, (![B_409, C_410, A_411]: (k1_xboole_0=B_409 | v1_funct_2(C_410, A_411, B_409) | k1_relset_1(A_411, B_409, C_410)!=A_411 | ~m1_subset_1(C_410, k1_zfmisc_1(k2_zfmisc_1(A_411, B_409))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.45/2.35  tff(c_3090, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_2861, c_3084])).
% 6.45/2.35  tff(c_3106, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2856, c_3090])).
% 6.45/2.35  tff(c_3107, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2862, c_71, c_3106])).
% 6.45/2.35  tff(c_3204, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3198, c_3107])).
% 6.45/2.35  tff(c_3250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_3204])).
% 6.45/2.35  tff(c_3251, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 6.45/2.35  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.45/2.35  tff(c_3272, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_3251, c_6])).
% 6.45/2.35  tff(c_3252, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 6.45/2.35  tff(c_3257, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_3252])).
% 6.45/2.35  tff(c_3258, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_62])).
% 6.45/2.35  tff(c_4452, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3258])).
% 6.45/2.35  tff(c_4454, plain, (![A_597, B_598]: (r1_tarski(A_597, B_598) | ~m1_subset_1(A_597, k1_zfmisc_1(B_598)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.35  tff(c_4458, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_4452, c_4454])).
% 6.45/2.35  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.45/2.35  tff(c_3294, plain, (![A_1]: (A_1='#skF_1' | ~r1_tarski(A_1, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_3251, c_2])).
% 6.45/2.35  tff(c_4462, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_4458, c_3294])).
% 6.45/2.35  tff(c_3259, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_64])).
% 6.45/2.35  tff(c_6502, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_3259])).
% 6.45/2.35  tff(c_3288, plain, (![A_432, B_433]: (v1_relat_1(k2_zfmisc_1(A_432, B_433)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.45/2.35  tff(c_3290, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3272, c_3288])).
% 6.45/2.35  tff(c_4471, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_3290])).
% 6.45/2.35  tff(c_24, plain, (![B_15, A_14]: (r1_tarski(k7_relat_1(B_15, A_14), B_15) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.45/2.35  tff(c_4528, plain, (![A_603]: (A_603='#skF_4' | ~r1_tarski(A_603, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_3294])).
% 6.45/2.35  tff(c_4535, plain, (![A_14]: (k7_relat_1('#skF_4', A_14)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_4528])).
% 6.45/2.35  tff(c_4540, plain, (![A_14]: (k7_relat_1('#skF_4', A_14)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_4535])).
% 6.45/2.35  tff(c_4563, plain, (![B_607, A_608]: (r1_tarski(k1_relat_1(k7_relat_1(B_607, A_608)), A_608) | ~v1_relat_1(B_607))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.45/2.35  tff(c_4570, plain, (![A_14]: (r1_tarski(k1_relat_1('#skF_4'), A_14) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4540, c_4563])).
% 6.45/2.35  tff(c_4574, plain, (![A_609]: (r1_tarski(k1_relat_1('#skF_4'), A_609))), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_4570])).
% 6.45/2.35  tff(c_4470, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_3294])).
% 6.45/2.35  tff(c_4579, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_4574, c_4470])).
% 6.45/2.35  tff(c_4573, plain, (![A_14]: (r1_tarski(k1_relat_1('#skF_4'), A_14))), inference(demodulation, [status(thm), theory('equality')], [c_4471, c_4570])).
% 6.45/2.35  tff(c_4580, plain, (![A_14]: (r1_tarski('#skF_4', A_14))), inference(demodulation, [status(thm), theory('equality')], [c_4579, c_4573])).
% 6.45/2.35  tff(c_4467, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4452])).
% 6.45/2.35  tff(c_4473, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_3272])).
% 6.45/2.35  tff(c_5520, plain, (![A_753, B_754, C_755, D_756]: (k2_partfun1(A_753, B_754, C_755, D_756)=k7_relat_1(C_755, D_756) | ~m1_subset_1(C_755, k1_zfmisc_1(k2_zfmisc_1(A_753, B_754))) | ~v1_funct_1(C_755))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.45/2.35  tff(c_6478, plain, (![A_860, C_861, D_862]: (k2_partfun1(A_860, '#skF_4', C_861, D_862)=k7_relat_1(C_861, D_862) | ~m1_subset_1(C_861, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_861))), inference(superposition, [status(thm), theory('equality')], [c_4473, c_5520])).
% 6.45/2.35  tff(c_6483, plain, (![A_860, D_862]: (k2_partfun1(A_860, '#skF_4', '#skF_4', D_862)=k7_relat_1('#skF_4', D_862) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_4467, c_6478])).
% 6.45/2.35  tff(c_6487, plain, (![A_860, D_862]: (k2_partfun1(A_860, '#skF_4', '#skF_4', D_862)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4540, c_6483])).
% 6.45/2.35  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.35  tff(c_3295, plain, (![A_434]: (A_434='#skF_1' | ~r1_tarski(A_434, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_3251, c_2])).
% 6.45/2.35  tff(c_3299, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_3295])).
% 6.45/2.35  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.45/2.35  tff(c_3264, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3251, c_3251, c_8])).
% 6.45/2.35  tff(c_3313, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3264, c_3258])).
% 6.45/2.35  tff(c_3341, plain, (![A_442, B_443]: (r1_tarski(A_442, B_443) | ~m1_subset_1(A_442, k1_zfmisc_1(B_443)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.35  tff(c_3349, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3313, c_3341])).
% 6.45/2.35  tff(c_3353, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_3349, c_3294])).
% 6.45/2.35  tff(c_3357, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_3313])).
% 6.45/2.35  tff(c_3364, plain, (![B_3]: (k2_zfmisc_1('#skF_4', B_3)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_3353, c_3264])).
% 6.45/2.35  tff(c_3937, plain, (![A_523, B_524, C_525, D_526]: (v1_funct_1(k2_partfun1(A_523, B_524, C_525, D_526)) | ~m1_subset_1(C_525, k1_zfmisc_1(k2_zfmisc_1(A_523, B_524))) | ~v1_funct_1(C_525))), inference(cnfTransformation, [status(thm)], [f_113])).
% 6.45/2.35  tff(c_4426, plain, (![B_592, C_593, D_594]: (v1_funct_1(k2_partfun1('#skF_4', B_592, C_593, D_594)) | ~m1_subset_1(C_593, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_593))), inference(superposition, [status(thm), theory('equality')], [c_3364, c_3937])).
% 6.45/2.35  tff(c_4428, plain, (![B_592, D_594]: (v1_funct_1(k2_partfun1('#skF_4', B_592, '#skF_4', D_594)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_3357, c_4426])).
% 6.45/2.35  tff(c_4434, plain, (![B_592, D_594]: (v1_funct_1(k2_partfun1('#skF_4', B_592, '#skF_4', D_594)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4428])).
% 6.45/2.35  tff(c_3300, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_3257, c_3257, c_3257, c_3272, c_3257, c_3257, c_56])).
% 6.45/2.35  tff(c_3301, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3300])).
% 6.45/2.35  tff(c_3314, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3299, c_3301])).
% 6.45/2.35  tff(c_3356, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_3353, c_3353, c_3353, c_3314])).
% 6.45/2.35  tff(c_4438, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4434, c_3356])).
% 6.45/2.35  tff(c_4439, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_3300])).
% 6.45/2.35  tff(c_4463, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3299, c_3299, c_3299, c_4439])).
% 6.45/2.35  tff(c_4464, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_4463])).
% 6.45/2.35  tff(c_4585, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_4462, c_4462, c_4464])).
% 6.45/2.35  tff(c_4589, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_12, c_4585])).
% 6.45/2.35  tff(c_6488, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6487, c_4589])).
% 6.45/2.35  tff(c_6492, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4580, c_6488])).
% 6.45/2.35  tff(c_6494, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_4463])).
% 6.45/2.35  tff(c_6696, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_4462, c_4462, c_6494])).
% 6.45/2.35  tff(c_10, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.45/2.35  tff(c_6704, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6696, c_10])).
% 6.45/2.35  tff(c_6500, plain, (![A_1]: (A_1='#skF_4' | ~r1_tarski(A_1, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_3294])).
% 6.45/2.35  tff(c_6772, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_6704, c_6500])).
% 6.45/2.35  tff(c_6493, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(splitRight, [status(thm)], [c_4463])).
% 6.45/2.35  tff(c_6593, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4462, c_4462, c_4462, c_4462, c_4462, c_6493])).
% 6.45/2.35  tff(c_6776, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6772, c_6593])).
% 6.45/2.35  tff(c_6783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6502, c_6776])).
% 6.45/2.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.45/2.35  
% 6.45/2.35  Inference rules
% 6.45/2.35  ----------------------
% 6.45/2.35  #Ref     : 0
% 6.45/2.35  #Sup     : 1422
% 6.45/2.35  #Fact    : 0
% 6.45/2.35  #Define  : 0
% 6.45/2.35  #Split   : 12
% 6.45/2.35  #Chain   : 0
% 6.45/2.35  #Close   : 0
% 6.45/2.35  
% 6.45/2.35  Ordering : KBO
% 6.45/2.35  
% 6.45/2.35  Simplification rules
% 6.45/2.35  ----------------------
% 6.45/2.35  #Subsume      : 139
% 6.45/2.35  #Demod        : 1495
% 6.45/2.35  #Tautology    : 714
% 6.45/2.35  #SimpNegUnit  : 8
% 6.45/2.35  #BackRed      : 75
% 6.45/2.35  
% 6.45/2.35  #Partial instantiations: 0
% 6.45/2.35  #Strategies tried      : 1
% 6.45/2.35  
% 6.45/2.35  Timing (in seconds)
% 6.45/2.35  ----------------------
% 6.45/2.36  Preprocessing        : 0.35
% 6.45/2.36  Parsing              : 0.18
% 6.45/2.36  CNF conversion       : 0.02
% 6.45/2.36  Main loop            : 1.15
% 6.45/2.36  Inferencing          : 0.43
% 6.45/2.36  Reduction            : 0.39
% 6.45/2.36  Demodulation         : 0.28
% 6.45/2.36  BG Simplification    : 0.04
% 6.45/2.36  Subsumption          : 0.19
% 6.45/2.36  Abstraction          : 0.05
% 6.45/2.36  MUC search           : 0.00
% 6.45/2.36  Cooper               : 0.00
% 6.45/2.36  Total                : 1.55
% 6.45/2.36  Index Insertion      : 0.00
% 6.45/2.36  Index Deletion       : 0.00
% 6.45/2.36  Index Matching       : 0.00
% 6.45/2.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
