%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:37 EST 2020

% Result     : Theorem 8.24s
% Output     : CNFRefutation 8.60s
% Verified   : 
% Statistics : Number of formulae       :  175 (3895 expanded)
%              Number of leaves         :   38 (1215 expanded)
%              Depth                    :   16
%              Number of atoms          :  274 (12103 expanded)
%              Number of equality atoms :   70 (4828 expanded)
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

tff(f_143,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_109,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_123,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_91,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_117,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

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

tff(c_60,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_4628,plain,(
    ! [C_511,A_512,B_513] :
      ( v1_relat_1(C_511)
      | ~ m1_subset_1(C_511,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4641,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_4628])).

tff(c_58,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_71,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_64,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_5560,plain,(
    ! [A_605,B_606,C_607] :
      ( k1_relset_1(A_605,B_606,C_607) = k1_relat_1(C_607)
      | ~ m1_subset_1(C_607,k1_zfmisc_1(k2_zfmisc_1(A_605,B_606))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_5579,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_5560])).

tff(c_6780,plain,(
    ! [B_715,A_716,C_717] :
      ( k1_xboole_0 = B_715
      | k1_relset_1(A_716,B_715,C_717) = A_716
      | ~ v1_funct_2(C_717,A_716,B_715)
      | ~ m1_subset_1(C_717,k1_zfmisc_1(k2_zfmisc_1(A_716,B_715))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_6790,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_6780])).

tff(c_6801,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5579,c_6790])).

tff(c_6802,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_6801])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_6808,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6802,c_26])).

tff(c_6812,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4641,c_6808])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_6705,plain,(
    ! [A_706,B_707,C_708,D_709] :
      ( k2_partfun1(A_706,B_707,C_708,D_709) = k7_relat_1(C_708,D_709)
      | ~ m1_subset_1(C_708,k1_zfmisc_1(k2_zfmisc_1(A_706,B_707)))
      | ~ v1_funct_1(C_708) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_6714,plain,(
    ! [D_709] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_709) = k7_relat_1('#skF_4',D_709)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_6705])).

tff(c_6726,plain,(
    ! [D_709] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_709) = k7_relat_1('#skF_4',D_709) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_6714])).

tff(c_2242,plain,(
    ! [C_278,A_279,B_280] :
      ( v1_relat_1(C_278)
      | ~ m1_subset_1(C_278,k1_zfmisc_1(k2_zfmisc_1(A_279,B_280))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2255,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_2242])).

tff(c_24,plain,(
    ! [B_16,A_15] :
      ( r1_tarski(k7_relat_1(B_16,A_15),B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2217,plain,(
    ! [A_272,B_273] :
      ( r1_tarski(A_272,B_273)
      | ~ m1_subset_1(A_272,k1_zfmisc_1(B_273)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2221,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_62,c_2217])).

tff(c_2484,plain,(
    ! [A_316,C_317,B_318] :
      ( r1_tarski(A_316,C_317)
      | ~ r1_tarski(B_318,C_317)
      | ~ r1_tarski(A_316,B_318) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2659,plain,(
    ! [A_329] :
      ( r1_tarski(A_329,k2_zfmisc_1('#skF_1','#skF_2'))
      | ~ r1_tarski(A_329,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2221,c_2484])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2395,plain,(
    ! [C_295,B_296,A_297] :
      ( v5_relat_1(C_295,B_296)
      | ~ m1_subset_1(C_295,k1_zfmisc_1(k2_zfmisc_1(A_297,B_296))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2409,plain,(
    ! [A_7,B_296,A_297] :
      ( v5_relat_1(A_7,B_296)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_297,B_296)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2395])).

tff(c_2677,plain,(
    ! [A_329] :
      ( v5_relat_1(A_329,'#skF_2')
      | ~ r1_tarski(A_329,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2659,c_2409])).

tff(c_2254,plain,(
    ! [A_7,A_279,B_280] :
      ( v1_relat_1(A_7)
      | ~ r1_tarski(A_7,k2_zfmisc_1(A_279,B_280)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2242])).

tff(c_2709,plain,(
    ! [A_332] :
      ( v1_relat_1(A_332)
      | ~ r1_tarski(A_332,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_2659,c_2254])).

tff(c_2725,plain,(
    ! [A_15] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_15))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_2709])).

tff(c_2732,plain,(
    ! [A_15] : v1_relat_1(k7_relat_1('#skF_4',A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_2725])).

tff(c_18,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k2_relat_1(B_10),A_9)
      | ~ v5_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [B_14,A_13] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_14,A_13)),A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_36,plain,(
    ! [C_30,A_28,B_29] :
      ( m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29)))
      | ~ r1_tarski(k2_relat_1(C_30),B_29)
      | ~ r1_tarski(k1_relat_1(C_30),A_28)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_4008,plain,(
    ! [A_460,B_461,C_462,D_463] :
      ( k2_partfun1(A_460,B_461,C_462,D_463) = k7_relat_1(C_462,D_463)
      | ~ m1_subset_1(C_462,k1_zfmisc_1(k2_zfmisc_1(A_460,B_461)))
      | ~ v1_funct_1(C_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_4015,plain,(
    ! [D_463] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_463) = k7_relat_1('#skF_4',D_463)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_4008])).

tff(c_4024,plain,(
    ! [D_463] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_463) = k7_relat_1('#skF_4',D_463) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4015])).

tff(c_2035,plain,(
    ! [A_241,B_242,C_243,D_244] :
      ( v1_funct_1(k2_partfun1(A_241,B_242,C_243,D_244))
      | ~ m1_subset_1(C_243,k1_zfmisc_1(k2_zfmisc_1(A_241,B_242)))
      | ~ v1_funct_1(C_243) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_2040,plain,(
    ! [D_244] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_244))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_2035])).

tff(c_2048,plain,(
    ! [D_244] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_244)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_2040])).

tff(c_56,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_95,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_2051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2048,c_95])).

tff(c_2052,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_2055,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_2052])).

tff(c_4027,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4024,c_2055])).

tff(c_4040,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_36,c_4027])).

tff(c_4046,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_4040])).

tff(c_4306,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_4046])).

tff(c_4312,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_4306])).

tff(c_4316,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_4312])).

tff(c_4317,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_4046])).

tff(c_4334,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_18,c_4317])).

tff(c_4340,plain,(
    ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2732,c_4334])).

tff(c_4353,plain,(
    ~ r1_tarski(k7_relat_1('#skF_4','#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_2677,c_4340])).

tff(c_4405,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_4353])).

tff(c_4409,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2255,c_4405])).

tff(c_4411,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_2052])).

tff(c_5577,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4411,c_5560])).

tff(c_6729,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6726,c_6726,c_5577])).

tff(c_4410,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_2052])).

tff(c_6740,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6726,c_4410])).

tff(c_6739,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6726,c_4411])).

tff(c_7050,plain,(
    ! [B_722,C_723,A_724] :
      ( k1_xboole_0 = B_722
      | v1_funct_2(C_723,A_724,B_722)
      | k1_relset_1(A_724,B_722,C_723) != A_724
      | ~ m1_subset_1(C_723,k1_zfmisc_1(k2_zfmisc_1(A_724,B_722))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_7053,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_6739,c_7050])).

tff(c_7072,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6740,c_71,c_7053])).

tff(c_7146,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6729,c_7072])).

tff(c_7153,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6812,c_7146])).

tff(c_7157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_7153])).

tff(c_7158,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_8,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7170,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7158,c_8])).

tff(c_7159,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_7164,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7159])).

tff(c_7194,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7170,c_7164,c_62])).

tff(c_7212,plain,(
    ! [A_734,B_735] :
      ( r1_tarski(A_734,B_735)
      | ~ m1_subset_1(A_734,k1_zfmisc_1(B_735)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7216,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_7194,c_7212])).

tff(c_4,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_7195,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7158,c_4])).

tff(c_7226,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_7216,c_7195])).

tff(c_7165,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7164,c_64])).

tff(c_7232,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7226,c_7165])).

tff(c_7217,plain,(
    ! [B_736,A_737] :
      ( r1_tarski(k7_relat_1(B_736,A_737),B_736)
      | ~ v1_relat_1(B_736) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_7222,plain,(
    ! [A_737] :
      ( k7_relat_1('#skF_1',A_737) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_7217,c_7195])).

tff(c_8716,plain,(
    ! [A_737] :
      ( k7_relat_1('#skF_4',A_737) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7226,c_7226,c_7222])).

tff(c_8717,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_8716])).

tff(c_7231,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7194])).

tff(c_7234,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7226,c_7170])).

tff(c_8737,plain,(
    ! [C_906,A_907,B_908] :
      ( v1_relat_1(C_906)
      | ~ m1_subset_1(C_906,k1_zfmisc_1(k2_zfmisc_1(A_907,B_908))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8747,plain,(
    ! [C_909] :
      ( v1_relat_1(C_909)
      | ~ m1_subset_1(C_909,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7234,c_8737])).

tff(c_8754,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_7231,c_8747])).

tff(c_8759,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8717,c_8754])).

tff(c_8761,plain,(
    v1_relat_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8716])).

tff(c_8760,plain,(
    ! [A_737] : k7_relat_1('#skF_4',A_737) = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_8716])).

tff(c_8783,plain,(
    ! [B_911,A_912] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_911,A_912)),A_912)
      | ~ v1_relat_1(B_911) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8790,plain,(
    ! [A_737] :
      ( r1_tarski(k1_relat_1('#skF_4'),A_737)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8760,c_8783])).

tff(c_8794,plain,(
    ! [A_913] : r1_tarski(k1_relat_1('#skF_4'),A_913) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8761,c_8790])).

tff(c_7230,plain,(
    ! [A_4] :
      ( A_4 = '#skF_4'
      | ~ r1_tarski(A_4,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7226,c_7195])).

tff(c_8799,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8794,c_7230])).

tff(c_8793,plain,(
    ! [A_737] : r1_tarski(k1_relat_1('#skF_4'),A_737) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8761,c_8790])).

tff(c_8800,plain,(
    ! [A_737] : r1_tarski('#skF_4',A_737) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8799,c_8793])).

tff(c_10071,plain,(
    ! [A_1061,B_1062,C_1063,D_1064] :
      ( k2_partfun1(A_1061,B_1062,C_1063,D_1064) = k7_relat_1(C_1063,D_1064)
      | ~ m1_subset_1(C_1063,k1_zfmisc_1(k2_zfmisc_1(A_1061,B_1062)))
      | ~ v1_funct_1(C_1063) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_12036,plain,(
    ! [A_1220,B_1221,A_1222,D_1223] :
      ( k2_partfun1(A_1220,B_1221,A_1222,D_1223) = k7_relat_1(A_1222,D_1223)
      | ~ v1_funct_1(A_1222)
      | ~ r1_tarski(A_1222,k2_zfmisc_1(A_1220,B_1221)) ) ),
    inference(resolution,[status(thm)],[c_14,c_10071])).

tff(c_12063,plain,(
    ! [A_1220,B_1221,D_1223] :
      ( k2_partfun1(A_1220,B_1221,'#skF_4',D_1223) = k7_relat_1('#skF_4',D_1223)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_8800,c_12036])).

tff(c_12084,plain,(
    ! [A_1220,B_1221,D_1223] : k2_partfun1(A_1220,B_1221,'#skF_4',D_1223) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8760,c_12063])).

tff(c_7235,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7164])).

tff(c_10,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7178,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7158,c_10])).

tff(c_7233,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7226,c_7178])).

tff(c_7993,plain,(
    ! [A_828,B_829,C_830,D_831] :
      ( v1_funct_1(k2_partfun1(A_828,B_829,C_830,D_831))
      | ~ m1_subset_1(C_830,k1_zfmisc_1(k2_zfmisc_1(A_828,B_829)))
      | ~ v1_funct_1(C_830) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_8648,plain,(
    ! [A_895,C_896,D_897] :
      ( v1_funct_1(k2_partfun1(A_895,'#skF_4',C_896,D_897))
      | ~ m1_subset_1(C_896,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_896) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7234,c_7993])).

tff(c_8650,plain,(
    ! [A_895,D_897] :
      ( v1_funct_1(k2_partfun1(A_895,'#skF_4','#skF_4',D_897))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_7231,c_8648])).

tff(c_8656,plain,(
    ! [A_895,D_897] : v1_funct_1(k2_partfun1(A_895,'#skF_4','#skF_4',D_897)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_8650])).

tff(c_7196,plain,(
    ! [A_731] :
      ( A_731 = '#skF_1'
      | ~ r1_tarski(A_731,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7158,c_7158,c_4])).

tff(c_7200,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60,c_7196])).

tff(c_7229,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7226,c_7200])).

tff(c_7245,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7229,c_7226,c_7229,c_7229,c_7226,c_7229,c_7229,c_7226,c_56])).

tff(c_7246,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_7245])).

tff(c_7288,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_7246])).

tff(c_8660,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8656,c_7288])).

tff(c_8661,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_7245])).

tff(c_8779,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7235,c_7233,c_7235,c_7235,c_8661])).

tff(c_8780,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8779])).

tff(c_8868,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_8780])).

tff(c_12089,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12084,c_8868])).

tff(c_12095,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8800,c_12089])).

tff(c_12097,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8779])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12208,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12097,c_12])).

tff(c_12238,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12208,c_7230])).

tff(c_12096,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_8779])).

tff(c_12242,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12238,c_12096])).

tff(c_12249,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7232,c_12242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:20:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.24/2.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.77  
% 8.24/2.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.24/2.77  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.24/2.77  
% 8.24/2.77  %Foreground sorts:
% 8.24/2.77  
% 8.24/2.77  
% 8.24/2.77  %Background operators:
% 8.24/2.77  
% 8.24/2.77  
% 8.24/2.77  %Foreground operators:
% 8.24/2.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.24/2.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.24/2.77  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.24/2.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.24/2.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.24/2.77  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.24/2.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.24/2.77  tff('#skF_2', type, '#skF_2': $i).
% 8.24/2.77  tff('#skF_3', type, '#skF_3': $i).
% 8.24/2.77  tff('#skF_1', type, '#skF_1': $i).
% 8.24/2.77  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.24/2.77  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.24/2.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.24/2.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.24/2.77  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.24/2.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.24/2.77  tff('#skF_4', type, '#skF_4': $i).
% 8.24/2.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.24/2.77  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.24/2.77  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.24/2.77  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.24/2.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.24/2.77  
% 8.60/2.79  tff(f_143, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 8.60/2.79  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.60/2.79  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.60/2.79  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.60/2.79  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.60/2.79  tff(f_123, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.60/2.79  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 8.60/2.79  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.60/2.79  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 8.60/2.79  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.60/2.79  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.60/2.79  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 8.60/2.79  tff(f_91, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 8.60/2.79  tff(f_117, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.60/2.79  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.60/2.79  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 8.60/2.79  tff(c_60, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_4628, plain, (![C_511, A_512, B_513]: (v1_relat_1(C_511) | ~m1_subset_1(C_511, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.60/2.79  tff(c_4641, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_4628])).
% 8.60/2.79  tff(c_58, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_71, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_58])).
% 8.60/2.79  tff(c_64, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_5560, plain, (![A_605, B_606, C_607]: (k1_relset_1(A_605, B_606, C_607)=k1_relat_1(C_607) | ~m1_subset_1(C_607, k1_zfmisc_1(k2_zfmisc_1(A_605, B_606))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.60/2.79  tff(c_5579, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_5560])).
% 8.60/2.79  tff(c_6780, plain, (![B_715, A_716, C_717]: (k1_xboole_0=B_715 | k1_relset_1(A_716, B_715, C_717)=A_716 | ~v1_funct_2(C_717, A_716, B_715) | ~m1_subset_1(C_717, k1_zfmisc_1(k2_zfmisc_1(A_716, B_715))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.60/2.79  tff(c_6790, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_6780])).
% 8.60/2.79  tff(c_6801, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5579, c_6790])).
% 8.60/2.79  tff(c_6802, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_71, c_6801])).
% 8.60/2.79  tff(c_26, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.60/2.79  tff(c_6808, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_6802, c_26])).
% 8.60/2.79  tff(c_6812, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_4641, c_6808])).
% 8.60/2.79  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_6705, plain, (![A_706, B_707, C_708, D_709]: (k2_partfun1(A_706, B_707, C_708, D_709)=k7_relat_1(C_708, D_709) | ~m1_subset_1(C_708, k1_zfmisc_1(k2_zfmisc_1(A_706, B_707))) | ~v1_funct_1(C_708))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.60/2.79  tff(c_6714, plain, (![D_709]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_709)=k7_relat_1('#skF_4', D_709) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_6705])).
% 8.60/2.79  tff(c_6726, plain, (![D_709]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_709)=k7_relat_1('#skF_4', D_709))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_6714])).
% 8.60/2.79  tff(c_2242, plain, (![C_278, A_279, B_280]: (v1_relat_1(C_278) | ~m1_subset_1(C_278, k1_zfmisc_1(k2_zfmisc_1(A_279, B_280))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.60/2.79  tff(c_2255, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_2242])).
% 8.60/2.79  tff(c_24, plain, (![B_16, A_15]: (r1_tarski(k7_relat_1(B_16, A_15), B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.60/2.79  tff(c_2217, plain, (![A_272, B_273]: (r1_tarski(A_272, B_273) | ~m1_subset_1(A_272, k1_zfmisc_1(B_273)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.60/2.79  tff(c_2221, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_62, c_2217])).
% 8.60/2.79  tff(c_2484, plain, (![A_316, C_317, B_318]: (r1_tarski(A_316, C_317) | ~r1_tarski(B_318, C_317) | ~r1_tarski(A_316, B_318))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.60/2.79  tff(c_2659, plain, (![A_329]: (r1_tarski(A_329, k2_zfmisc_1('#skF_1', '#skF_2')) | ~r1_tarski(A_329, '#skF_4'))), inference(resolution, [status(thm)], [c_2221, c_2484])).
% 8.60/2.79  tff(c_14, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.60/2.79  tff(c_2395, plain, (![C_295, B_296, A_297]: (v5_relat_1(C_295, B_296) | ~m1_subset_1(C_295, k1_zfmisc_1(k2_zfmisc_1(A_297, B_296))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.60/2.79  tff(c_2409, plain, (![A_7, B_296, A_297]: (v5_relat_1(A_7, B_296) | ~r1_tarski(A_7, k2_zfmisc_1(A_297, B_296)))), inference(resolution, [status(thm)], [c_14, c_2395])).
% 8.60/2.79  tff(c_2677, plain, (![A_329]: (v5_relat_1(A_329, '#skF_2') | ~r1_tarski(A_329, '#skF_4'))), inference(resolution, [status(thm)], [c_2659, c_2409])).
% 8.60/2.79  tff(c_2254, plain, (![A_7, A_279, B_280]: (v1_relat_1(A_7) | ~r1_tarski(A_7, k2_zfmisc_1(A_279, B_280)))), inference(resolution, [status(thm)], [c_14, c_2242])).
% 8.60/2.79  tff(c_2709, plain, (![A_332]: (v1_relat_1(A_332) | ~r1_tarski(A_332, '#skF_4'))), inference(resolution, [status(thm)], [c_2659, c_2254])).
% 8.60/2.79  tff(c_2725, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_2709])).
% 8.60/2.79  tff(c_2732, plain, (![A_15]: (v1_relat_1(k7_relat_1('#skF_4', A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_2255, c_2725])).
% 8.60/2.79  tff(c_18, plain, (![B_10, A_9]: (r1_tarski(k2_relat_1(B_10), A_9) | ~v5_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_51])).
% 8.60/2.79  tff(c_22, plain, (![B_14, A_13]: (r1_tarski(k1_relat_1(k7_relat_1(B_14, A_13)), A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.60/2.79  tff(c_36, plain, (![C_30, A_28, B_29]: (m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))) | ~r1_tarski(k2_relat_1(C_30), B_29) | ~r1_tarski(k1_relat_1(C_30), A_28) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_91])).
% 8.60/2.79  tff(c_4008, plain, (![A_460, B_461, C_462, D_463]: (k2_partfun1(A_460, B_461, C_462, D_463)=k7_relat_1(C_462, D_463) | ~m1_subset_1(C_462, k1_zfmisc_1(k2_zfmisc_1(A_460, B_461))) | ~v1_funct_1(C_462))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.60/2.79  tff(c_4015, plain, (![D_463]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_463)=k7_relat_1('#skF_4', D_463) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_4008])).
% 8.60/2.79  tff(c_4024, plain, (![D_463]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_463)=k7_relat_1('#skF_4', D_463))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4015])).
% 8.60/2.79  tff(c_2035, plain, (![A_241, B_242, C_243, D_244]: (v1_funct_1(k2_partfun1(A_241, B_242, C_243, D_244)) | ~m1_subset_1(C_243, k1_zfmisc_1(k2_zfmisc_1(A_241, B_242))) | ~v1_funct_1(C_243))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.60/2.79  tff(c_2040, plain, (![D_244]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_244)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_62, c_2035])).
% 8.60/2.79  tff(c_2048, plain, (![D_244]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_244)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_2040])).
% 8.60/2.79  tff(c_56, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_143])).
% 8.60/2.79  tff(c_95, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_56])).
% 8.60/2.79  tff(c_2051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2048, c_95])).
% 8.60/2.79  tff(c_2052, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_56])).
% 8.60/2.79  tff(c_2055, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_2052])).
% 8.60/2.79  tff(c_4027, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4024, c_2055])).
% 8.60/2.79  tff(c_4040, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_36, c_4027])).
% 8.60/2.79  tff(c_4046, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2732, c_4040])).
% 8.60/2.79  tff(c_4306, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(splitLeft, [status(thm)], [c_4046])).
% 8.60/2.79  tff(c_4312, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_22, c_4306])).
% 8.60/2.79  tff(c_4316, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2255, c_4312])).
% 8.60/2.79  tff(c_4317, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(splitRight, [status(thm)], [c_4046])).
% 8.60/2.79  tff(c_4334, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_18, c_4317])).
% 8.60/2.79  tff(c_4340, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2732, c_4334])).
% 8.60/2.79  tff(c_4353, plain, (~r1_tarski(k7_relat_1('#skF_4', '#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_2677, c_4340])).
% 8.60/2.79  tff(c_4405, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_4353])).
% 8.60/2.79  tff(c_4409, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2255, c_4405])).
% 8.60/2.79  tff(c_4411, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_2052])).
% 8.60/2.79  tff(c_5577, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_4411, c_5560])).
% 8.60/2.79  tff(c_6729, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6726, c_6726, c_5577])).
% 8.60/2.79  tff(c_4410, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_2052])).
% 8.60/2.79  tff(c_6740, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6726, c_4410])).
% 8.60/2.79  tff(c_6739, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_6726, c_4411])).
% 8.60/2.79  tff(c_7050, plain, (![B_722, C_723, A_724]: (k1_xboole_0=B_722 | v1_funct_2(C_723, A_724, B_722) | k1_relset_1(A_724, B_722, C_723)!=A_724 | ~m1_subset_1(C_723, k1_zfmisc_1(k2_zfmisc_1(A_724, B_722))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.60/2.79  tff(c_7053, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_6739, c_7050])).
% 8.60/2.79  tff(c_7072, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6740, c_71, c_7053])).
% 8.60/2.79  tff(c_7146, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6729, c_7072])).
% 8.60/2.79  tff(c_7153, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6812, c_7146])).
% 8.60/2.79  tff(c_7157, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_7153])).
% 8.60/2.79  tff(c_7158, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_58])).
% 8.60/2.79  tff(c_8, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.60/2.79  tff(c_7170, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7158, c_8])).
% 8.60/2.79  tff(c_7159, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_58])).
% 8.60/2.79  tff(c_7164, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7159])).
% 8.60/2.79  tff(c_7194, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7170, c_7164, c_62])).
% 8.60/2.79  tff(c_7212, plain, (![A_734, B_735]: (r1_tarski(A_734, B_735) | ~m1_subset_1(A_734, k1_zfmisc_1(B_735)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.60/2.79  tff(c_7216, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_7194, c_7212])).
% 8.60/2.79  tff(c_4, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.60/2.79  tff(c_7195, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7158, c_4])).
% 8.60/2.79  tff(c_7226, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_7216, c_7195])).
% 8.60/2.79  tff(c_7165, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7164, c_64])).
% 8.60/2.79  tff(c_7232, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7226, c_7165])).
% 8.60/2.79  tff(c_7217, plain, (![B_736, A_737]: (r1_tarski(k7_relat_1(B_736, A_737), B_736) | ~v1_relat_1(B_736))), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.60/2.79  tff(c_7222, plain, (![A_737]: (k7_relat_1('#skF_1', A_737)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_7217, c_7195])).
% 8.60/2.79  tff(c_8716, plain, (![A_737]: (k7_relat_1('#skF_4', A_737)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7226, c_7226, c_7222])).
% 8.60/2.79  tff(c_8717, plain, (~v1_relat_1('#skF_4')), inference(splitLeft, [status(thm)], [c_8716])).
% 8.60/2.79  tff(c_7231, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7194])).
% 8.60/2.79  tff(c_7234, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7226, c_7170])).
% 8.60/2.79  tff(c_8737, plain, (![C_906, A_907, B_908]: (v1_relat_1(C_906) | ~m1_subset_1(C_906, k1_zfmisc_1(k2_zfmisc_1(A_907, B_908))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.60/2.79  tff(c_8747, plain, (![C_909]: (v1_relat_1(C_909) | ~m1_subset_1(C_909, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_7234, c_8737])).
% 8.60/2.79  tff(c_8754, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_7231, c_8747])).
% 8.60/2.79  tff(c_8759, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8717, c_8754])).
% 8.60/2.79  tff(c_8761, plain, (v1_relat_1('#skF_4')), inference(splitRight, [status(thm)], [c_8716])).
% 8.60/2.79  tff(c_8760, plain, (![A_737]: (k7_relat_1('#skF_4', A_737)='#skF_4')), inference(splitRight, [status(thm)], [c_8716])).
% 8.60/2.79  tff(c_8783, plain, (![B_911, A_912]: (r1_tarski(k1_relat_1(k7_relat_1(B_911, A_912)), A_912) | ~v1_relat_1(B_911))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.60/2.79  tff(c_8790, plain, (![A_737]: (r1_tarski(k1_relat_1('#skF_4'), A_737) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8760, c_8783])).
% 8.60/2.79  tff(c_8794, plain, (![A_913]: (r1_tarski(k1_relat_1('#skF_4'), A_913))), inference(demodulation, [status(thm), theory('equality')], [c_8761, c_8790])).
% 8.60/2.79  tff(c_7230, plain, (![A_4]: (A_4='#skF_4' | ~r1_tarski(A_4, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7226, c_7195])).
% 8.60/2.79  tff(c_8799, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_8794, c_7230])).
% 8.60/2.79  tff(c_8793, plain, (![A_737]: (r1_tarski(k1_relat_1('#skF_4'), A_737))), inference(demodulation, [status(thm), theory('equality')], [c_8761, c_8790])).
% 8.60/2.79  tff(c_8800, plain, (![A_737]: (r1_tarski('#skF_4', A_737))), inference(demodulation, [status(thm), theory('equality')], [c_8799, c_8793])).
% 8.60/2.79  tff(c_10071, plain, (![A_1061, B_1062, C_1063, D_1064]: (k2_partfun1(A_1061, B_1062, C_1063, D_1064)=k7_relat_1(C_1063, D_1064) | ~m1_subset_1(C_1063, k1_zfmisc_1(k2_zfmisc_1(A_1061, B_1062))) | ~v1_funct_1(C_1063))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.60/2.79  tff(c_12036, plain, (![A_1220, B_1221, A_1222, D_1223]: (k2_partfun1(A_1220, B_1221, A_1222, D_1223)=k7_relat_1(A_1222, D_1223) | ~v1_funct_1(A_1222) | ~r1_tarski(A_1222, k2_zfmisc_1(A_1220, B_1221)))), inference(resolution, [status(thm)], [c_14, c_10071])).
% 8.60/2.79  tff(c_12063, plain, (![A_1220, B_1221, D_1223]: (k2_partfun1(A_1220, B_1221, '#skF_4', D_1223)=k7_relat_1('#skF_4', D_1223) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_8800, c_12036])).
% 8.60/2.79  tff(c_12084, plain, (![A_1220, B_1221, D_1223]: (k2_partfun1(A_1220, B_1221, '#skF_4', D_1223)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8760, c_12063])).
% 8.60/2.79  tff(c_7235, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7164])).
% 8.60/2.79  tff(c_10, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.60/2.79  tff(c_7178, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7158, c_10])).
% 8.60/2.79  tff(c_7233, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7226, c_7178])).
% 8.60/2.79  tff(c_7993, plain, (![A_828, B_829, C_830, D_831]: (v1_funct_1(k2_partfun1(A_828, B_829, C_830, D_831)) | ~m1_subset_1(C_830, k1_zfmisc_1(k2_zfmisc_1(A_828, B_829))) | ~v1_funct_1(C_830))), inference(cnfTransformation, [status(thm)], [f_117])).
% 8.60/2.79  tff(c_8648, plain, (![A_895, C_896, D_897]: (v1_funct_1(k2_partfun1(A_895, '#skF_4', C_896, D_897)) | ~m1_subset_1(C_896, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_896))), inference(superposition, [status(thm), theory('equality')], [c_7234, c_7993])).
% 8.60/2.79  tff(c_8650, plain, (![A_895, D_897]: (v1_funct_1(k2_partfun1(A_895, '#skF_4', '#skF_4', D_897)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_7231, c_8648])).
% 8.60/2.79  tff(c_8656, plain, (![A_895, D_897]: (v1_funct_1(k2_partfun1(A_895, '#skF_4', '#skF_4', D_897)))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_8650])).
% 8.60/2.79  tff(c_7196, plain, (![A_731]: (A_731='#skF_1' | ~r1_tarski(A_731, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_7158, c_7158, c_4])).
% 8.60/2.79  tff(c_7200, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_60, c_7196])).
% 8.60/2.79  tff(c_7229, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_7226, c_7200])).
% 8.60/2.79  tff(c_7245, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7229, c_7226, c_7229, c_7229, c_7226, c_7229, c_7229, c_7226, c_56])).
% 8.60/2.79  tff(c_7246, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_7245])).
% 8.60/2.79  tff(c_7288, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7235, c_7246])).
% 8.60/2.79  tff(c_8660, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8656, c_7288])).
% 8.60/2.79  tff(c_8661, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(splitRight, [status(thm)], [c_7245])).
% 8.60/2.79  tff(c_8779, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_7235, c_7233, c_7235, c_7235, c_8661])).
% 8.60/2.79  tff(c_8780, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8779])).
% 8.60/2.79  tff(c_8868, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_14, c_8780])).
% 8.60/2.79  tff(c_12089, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12084, c_8868])).
% 8.60/2.79  tff(c_12095, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8800, c_12089])).
% 8.60/2.79  tff(c_12097, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8779])).
% 8.60/2.79  tff(c_12, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.60/2.79  tff(c_12208, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_12097, c_12])).
% 8.60/2.79  tff(c_12238, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_12208, c_7230])).
% 8.60/2.79  tff(c_12096, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_8779])).
% 8.60/2.79  tff(c_12242, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12238, c_12096])).
% 8.60/2.79  tff(c_12249, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7232, c_12242])).
% 8.60/2.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.60/2.79  
% 8.60/2.79  Inference rules
% 8.60/2.79  ----------------------
% 8.60/2.79  #Ref     : 0
% 8.60/2.79  #Sup     : 2606
% 8.60/2.79  #Fact    : 0
% 8.60/2.79  #Define  : 0
% 8.60/2.79  #Split   : 27
% 8.60/2.79  #Chain   : 0
% 8.60/2.79  #Close   : 0
% 8.60/2.79  
% 8.60/2.79  Ordering : KBO
% 8.60/2.79  
% 8.60/2.79  Simplification rules
% 8.60/2.79  ----------------------
% 8.60/2.79  #Subsume      : 540
% 8.60/2.79  #Demod        : 1884
% 8.60/2.79  #Tautology    : 935
% 8.60/2.79  #SimpNegUnit  : 11
% 8.60/2.79  #BackRed      : 52
% 8.60/2.79  
% 8.60/2.79  #Partial instantiations: 0
% 8.60/2.79  #Strategies tried      : 1
% 8.60/2.79  
% 8.60/2.79  Timing (in seconds)
% 8.60/2.79  ----------------------
% 8.60/2.80  Preprocessing        : 0.33
% 8.60/2.80  Parsing              : 0.18
% 8.60/2.80  CNF conversion       : 0.02
% 8.60/2.80  Main loop            : 1.67
% 8.60/2.80  Inferencing          : 0.60
% 8.60/2.80  Reduction            : 0.54
% 8.60/2.80  Demodulation         : 0.37
% 8.60/2.80  BG Simplification    : 0.06
% 8.60/2.80  Subsumption          : 0.34
% 8.60/2.80  Abstraction          : 0.07
% 8.60/2.80  MUC search           : 0.00
% 8.60/2.80  Cooper               : 0.00
% 8.60/2.80  Total                : 2.06
% 8.60/2.80  Index Insertion      : 0.00
% 8.60/2.80  Index Deletion       : 0.00
% 8.60/2.80  Index Matching       : 0.00
% 8.60/2.80  BG Taut test         : 0.00
%------------------------------------------------------------------------------
