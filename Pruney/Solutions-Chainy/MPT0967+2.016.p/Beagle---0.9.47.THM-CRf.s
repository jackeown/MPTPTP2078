%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:15 EST 2020

% Result     : Theorem 4.73s
% Output     : CNFRefutation 4.73s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 396 expanded)
%              Number of leaves         :   35 ( 141 expanded)
%              Depth                    :   11
%              Number of atoms          :  154 (1162 expanded)
%              Number of equality atoms :   35 ( 398 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_128,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_108,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r1_tarski(k2_relset_1(A,B,D),C)
       => ( ( B = k1_xboole_0
            & A != k1_xboole_0 )
          | ( v1_funct_1(D)
            & v1_funct_2(D,A,C)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_40,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(c_72,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_62,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_74,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62])).

tff(c_225,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_101,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_70,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_68,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_672,plain,(
    ! [A_110,B_111,C_112] :
      ( m1_subset_1(k2_relset_1(A_110,B_111,C_112),k1_zfmisc_1(B_111))
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_24,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1295,plain,(
    ! [A_188,B_189,C_190] :
      ( r1_tarski(k2_relset_1(A_188,B_189,C_190),B_189)
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189))) ) ),
    inference(resolution,[status(thm)],[c_672,c_24])).

tff(c_1316,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_1295])).

tff(c_66,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_456,plain,(
    ! [A_85,C_86,B_87] :
      ( r1_tarski(A_85,C_86)
      | ~ r1_tarski(B_87,C_86)
      | ~ r1_tarski(A_85,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_471,plain,(
    ! [A_85] :
      ( r1_tarski(A_85,'#skF_3')
      | ~ r1_tarski(A_85,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_456])).

tff(c_1334,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1316,c_471])).

tff(c_56,plain,(
    ! [B_27,D_29,A_26,C_28] :
      ( k1_xboole_0 = B_27
      | v1_funct_2(D_29,A_26,C_28)
      | ~ r1_tarski(k2_relset_1(A_26,B_27,D_29),C_28)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(D_29,A_26,B_27)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1511,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1334,c_56])).

tff(c_1524,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_1511])).

tff(c_1526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_225,c_101,c_1524])).

tff(c_1527,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_2043,plain,(
    ! [A_260,B_261,C_262] :
      ( m1_subset_1(k2_relset_1(A_260,B_261,C_262),k1_zfmisc_1(B_261))
      | ~ m1_subset_1(C_262,k1_zfmisc_1(k2_zfmisc_1(A_260,B_261))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2803,plain,(
    ! [A_350,B_351,C_352] :
      ( r1_tarski(k2_relset_1(A_350,B_351,C_352),B_351)
      | ~ m1_subset_1(C_352,k1_zfmisc_1(k2_zfmisc_1(A_350,B_351))) ) ),
    inference(resolution,[status(thm)],[c_2043,c_24])).

tff(c_2824,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_68,c_2803])).

tff(c_1679,plain,(
    ! [A_221,C_222,B_223] :
      ( r1_tarski(A_221,C_222)
      | ~ r1_tarski(B_223,C_222)
      | ~ r1_tarski(A_221,B_223) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1694,plain,(
    ! [A_221] :
      ( r1_tarski(A_221,'#skF_3')
      | ~ r1_tarski(A_221,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_66,c_1679])).

tff(c_2848,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2824,c_1694])).

tff(c_52,plain,(
    ! [B_27,D_29,A_26,C_28] :
      ( k1_xboole_0 = B_27
      | m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,C_28)))
      | ~ r1_tarski(k2_relset_1(A_26,B_27,D_29),C_28)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27)))
      | ~ v1_funct_2(D_29,A_26,B_27)
      | ~ v1_funct_1(D_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2988,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2848,c_52])).

tff(c_2999,plain,
    ( k1_xboole_0 = '#skF_2'
    | m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_68,c_2988])).

tff(c_3001,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1527,c_101,c_2999])).

tff(c_3002,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_3005,plain,(
    ! [A_6] : r1_tarski('#skF_1',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_12])).

tff(c_18,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_3042,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_3002,c_18])).

tff(c_3003,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_3014,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_3003])).

tff(c_3067,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3042,c_3014,c_68])).

tff(c_3068,plain,(
    ! [A_362,B_363] :
      ( r1_tarski(A_362,B_363)
      | ~ m1_subset_1(A_362,k1_zfmisc_1(B_363)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_3075,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_3067,c_3068])).

tff(c_3085,plain,(
    ! [B_366,A_367] :
      ( B_366 = A_367
      | ~ r1_tarski(B_366,A_367)
      | ~ r1_tarski(A_367,B_366) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_3087,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_3075,c_3085])).

tff(c_3094,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3005,c_3087])).

tff(c_20,plain,(
    ! [A_9] : k1_subset_1(A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_22,plain,(
    ! [A_10] : m1_subset_1(k1_subset_1(A_10),k1_zfmisc_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_75,plain,(
    ! [A_10] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22])).

tff(c_3004,plain,(
    ! [A_10] : m1_subset_1('#skF_1',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_75])).

tff(c_3103,plain,(
    ! [A_10] : m1_subset_1('#skF_4',k1_zfmisc_1(A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3004])).

tff(c_3171,plain,(
    ! [C_374,A_375,B_376] :
      ( v1_relat_1(C_374)
      | ~ m1_subset_1(C_374,k1_zfmisc_1(k2_zfmisc_1(A_375,B_376))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_3182,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3103,c_3171])).

tff(c_3110,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3005])).

tff(c_32,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3007,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_3002,c_32])).

tff(c_3107,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3094,c_3007])).

tff(c_34,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_3008,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3002,c_3002,c_34])).

tff(c_3109,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3094,c_3008])).

tff(c_3449,plain,(
    ! [B_421,A_422] :
      ( v1_funct_2(B_421,k1_relat_1(B_421),A_422)
      | ~ r1_tarski(k2_relat_1(B_421),A_422)
      | ~ v1_funct_1(B_421)
      | ~ v1_relat_1(B_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_3452,plain,(
    ! [A_422] :
      ( v1_funct_2('#skF_4','#skF_4',A_422)
      | ~ r1_tarski(k2_relat_1('#skF_4'),A_422)
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3109,c_3449])).

tff(c_3454,plain,(
    ! [A_422] : v1_funct_2('#skF_4','#skF_4',A_422) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3182,c_72,c_3110,c_3107,c_3452])).

tff(c_3079,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3067,c_3042,c_74])).

tff(c_3100,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3094,c_3079])).

tff(c_3458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3454,c_3100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.73/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.96  
% 4.73/1.96  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.96  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_subset_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.73/1.96  
% 4.73/1.96  %Foreground sorts:
% 4.73/1.96  
% 4.73/1.96  
% 4.73/1.96  %Background operators:
% 4.73/1.96  
% 4.73/1.96  
% 4.73/1.96  %Foreground operators:
% 4.73/1.96  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.73/1.96  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 4.73/1.96  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.73/1.96  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.73/1.96  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.73/1.96  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.73/1.96  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.73/1.96  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.73/1.96  tff('#skF_2', type, '#skF_2': $i).
% 4.73/1.96  tff('#skF_3', type, '#skF_3': $i).
% 4.73/1.96  tff('#skF_1', type, '#skF_1': $i).
% 4.73/1.96  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.73/1.96  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.73/1.96  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.73/1.96  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.73/1.96  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.73/1.96  tff('#skF_4', type, '#skF_4': $i).
% 4.73/1.96  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.73/1.96  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.73/1.96  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.73/1.96  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.73/1.96  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.73/1.96  
% 4.73/1.98  tff(f_128, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 4.73/1.98  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.73/1.98  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.73/1.98  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.73/1.98  tff(f_108, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 4.73/1.98  tff(f_40, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.73/1.98  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 4.73/1.98  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.73/1.98  tff(f_48, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 4.73/1.98  tff(f_50, axiom, (![A]: m1_subset_1(k1_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_subset_1)).
% 4.73/1.98  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.73/1.98  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 4.73/1.98  tff(f_89, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 4.73/1.98  tff(c_72, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_62, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_74, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62])).
% 4.73/1.98  tff(c_225, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_74])).
% 4.73/1.98  tff(c_64, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_101, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_64])).
% 4.73/1.98  tff(c_70, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_68, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_672, plain, (![A_110, B_111, C_112]: (m1_subset_1(k2_relset_1(A_110, B_111, C_112), k1_zfmisc_1(B_111)) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.73/1.98  tff(c_24, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.98  tff(c_1295, plain, (![A_188, B_189, C_190]: (r1_tarski(k2_relset_1(A_188, B_189, C_190), B_189) | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))))), inference(resolution, [status(thm)], [c_672, c_24])).
% 4.73/1.98  tff(c_1316, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_1295])).
% 4.73/1.98  tff(c_66, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_128])).
% 4.73/1.98  tff(c_456, plain, (![A_85, C_86, B_87]: (r1_tarski(A_85, C_86) | ~r1_tarski(B_87, C_86) | ~r1_tarski(A_85, B_87))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.73/1.98  tff(c_471, plain, (![A_85]: (r1_tarski(A_85, '#skF_3') | ~r1_tarski(A_85, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_456])).
% 4.73/1.98  tff(c_1334, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_1316, c_471])).
% 4.73/1.98  tff(c_56, plain, (![B_27, D_29, A_26, C_28]: (k1_xboole_0=B_27 | v1_funct_2(D_29, A_26, C_28) | ~r1_tarski(k2_relset_1(A_26, B_27, D_29), C_28) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(D_29, A_26, B_27) | ~v1_funct_1(D_29))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.98  tff(c_1511, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1334, c_56])).
% 4.73/1.98  tff(c_1524, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_1511])).
% 4.73/1.98  tff(c_1526, plain, $false, inference(negUnitSimplification, [status(thm)], [c_225, c_101, c_1524])).
% 4.73/1.98  tff(c_1527, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_74])).
% 4.73/1.98  tff(c_2043, plain, (![A_260, B_261, C_262]: (m1_subset_1(k2_relset_1(A_260, B_261, C_262), k1_zfmisc_1(B_261)) | ~m1_subset_1(C_262, k1_zfmisc_1(k2_zfmisc_1(A_260, B_261))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.73/1.98  tff(c_2803, plain, (![A_350, B_351, C_352]: (r1_tarski(k2_relset_1(A_350, B_351, C_352), B_351) | ~m1_subset_1(C_352, k1_zfmisc_1(k2_zfmisc_1(A_350, B_351))))), inference(resolution, [status(thm)], [c_2043, c_24])).
% 4.73/1.98  tff(c_2824, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_68, c_2803])).
% 4.73/1.98  tff(c_1679, plain, (![A_221, C_222, B_223]: (r1_tarski(A_221, C_222) | ~r1_tarski(B_223, C_222) | ~r1_tarski(A_221, B_223))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.73/1.98  tff(c_1694, plain, (![A_221]: (r1_tarski(A_221, '#skF_3') | ~r1_tarski(A_221, '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_1679])).
% 4.73/1.98  tff(c_2848, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2824, c_1694])).
% 4.73/1.98  tff(c_52, plain, (![B_27, D_29, A_26, C_28]: (k1_xboole_0=B_27 | m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, C_28))) | ~r1_tarski(k2_relset_1(A_26, B_27, D_29), C_28) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))) | ~v1_funct_2(D_29, A_26, B_27) | ~v1_funct_1(D_29))), inference(cnfTransformation, [status(thm)], [f_108])).
% 4.73/1.98  tff(c_2988, plain, (k1_xboole_0='#skF_2' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_2848, c_52])).
% 4.73/1.98  tff(c_2999, plain, (k1_xboole_0='#skF_2' | m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_68, c_2988])).
% 4.73/1.98  tff(c_3001, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1527, c_101, c_2999])).
% 4.73/1.98  tff(c_3002, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_64])).
% 4.73/1.98  tff(c_12, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 4.73/1.98  tff(c_3005, plain, (![A_6]: (r1_tarski('#skF_1', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_12])).
% 4.73/1.98  tff(c_18, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.73/1.98  tff(c_3042, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_3002, c_18])).
% 4.73/1.98  tff(c_3003, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_64])).
% 4.73/1.98  tff(c_3014, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_3003])).
% 4.73/1.98  tff(c_3067, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_3042, c_3014, c_68])).
% 4.73/1.98  tff(c_3068, plain, (![A_362, B_363]: (r1_tarski(A_362, B_363) | ~m1_subset_1(A_362, k1_zfmisc_1(B_363)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.73/1.98  tff(c_3075, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_3067, c_3068])).
% 4.73/1.98  tff(c_3085, plain, (![B_366, A_367]: (B_366=A_367 | ~r1_tarski(B_366, A_367) | ~r1_tarski(A_367, B_366))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.73/1.98  tff(c_3087, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_3075, c_3085])).
% 4.73/1.98  tff(c_3094, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3005, c_3087])).
% 4.73/1.98  tff(c_20, plain, (![A_9]: (k1_subset_1(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.73/1.98  tff(c_22, plain, (![A_10]: (m1_subset_1(k1_subset_1(A_10), k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.73/1.98  tff(c_75, plain, (![A_10]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22])).
% 4.73/1.98  tff(c_3004, plain, (![A_10]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_75])).
% 4.73/1.98  tff(c_3103, plain, (![A_10]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3004])).
% 4.73/1.98  tff(c_3171, plain, (![C_374, A_375, B_376]: (v1_relat_1(C_374) | ~m1_subset_1(C_374, k1_zfmisc_1(k2_zfmisc_1(A_375, B_376))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.73/1.98  tff(c_3182, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3103, c_3171])).
% 4.73/1.98  tff(c_3110, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3005])).
% 4.73/1.98  tff(c_32, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.73/1.98  tff(c_3007, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_3002, c_32])).
% 4.73/1.98  tff(c_3107, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3094, c_3007])).
% 4.73/1.98  tff(c_34, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.73/1.98  tff(c_3008, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3002, c_3002, c_34])).
% 4.73/1.98  tff(c_3109, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3094, c_3008])).
% 4.73/1.98  tff(c_3449, plain, (![B_421, A_422]: (v1_funct_2(B_421, k1_relat_1(B_421), A_422) | ~r1_tarski(k2_relat_1(B_421), A_422) | ~v1_funct_1(B_421) | ~v1_relat_1(B_421))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.73/1.98  tff(c_3452, plain, (![A_422]: (v1_funct_2('#skF_4', '#skF_4', A_422) | ~r1_tarski(k2_relat_1('#skF_4'), A_422) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3109, c_3449])).
% 4.73/1.98  tff(c_3454, plain, (![A_422]: (v1_funct_2('#skF_4', '#skF_4', A_422))), inference(demodulation, [status(thm), theory('equality')], [c_3182, c_72, c_3110, c_3107, c_3452])).
% 4.73/1.98  tff(c_3079, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3067, c_3042, c_74])).
% 4.73/1.98  tff(c_3100, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_3094, c_3079])).
% 4.73/1.98  tff(c_3458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3454, c_3100])).
% 4.73/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.73/1.98  
% 4.73/1.98  Inference rules
% 4.73/1.98  ----------------------
% 4.73/1.98  #Ref     : 0
% 4.73/1.98  #Sup     : 714
% 4.73/1.98  #Fact    : 0
% 4.73/1.98  #Define  : 0
% 4.73/1.98  #Split   : 9
% 4.73/1.98  #Chain   : 0
% 4.73/1.98  #Close   : 0
% 4.73/1.98  
% 4.73/1.98  Ordering : KBO
% 4.73/1.98  
% 4.73/1.98  Simplification rules
% 4.73/1.98  ----------------------
% 4.73/1.98  #Subsume      : 144
% 4.73/1.98  #Demod        : 749
% 4.73/1.98  #Tautology    : 285
% 4.73/1.98  #SimpNegUnit  : 9
% 4.73/1.98  #BackRed      : 25
% 4.73/1.98  
% 4.73/1.98  #Partial instantiations: 0
% 4.73/1.98  #Strategies tried      : 1
% 4.73/1.98  
% 4.73/1.98  Timing (in seconds)
% 4.73/1.98  ----------------------
% 4.73/1.98  Preprocessing        : 0.38
% 4.73/1.98  Parsing              : 0.20
% 4.73/1.98  CNF conversion       : 0.02
% 4.73/1.98  Main loop            : 0.76
% 4.73/1.98  Inferencing          : 0.26
% 4.73/1.98  Reduction            : 0.26
% 4.73/1.98  Demodulation         : 0.18
% 4.73/1.98  BG Simplification    : 0.03
% 4.73/1.98  Subsumption          : 0.15
% 4.73/1.98  Abstraction          : 0.03
% 4.73/1.98  MUC search           : 0.00
% 4.73/1.98  Cooper               : 0.00
% 4.73/1.98  Total                : 1.18
% 4.73/1.98  Index Insertion      : 0.00
% 4.73/1.98  Index Deletion       : 0.00
% 4.73/1.98  Index Matching       : 0.00
% 4.73/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------
