%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:48 EST 2020

% Result     : Theorem 7.38s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :  119 ( 445 expanded)
%              Number of leaves         :   53 ( 164 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 (1156 expanded)
%              Number of equality atoms :   54 ( 527 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_4 > #skF_15 > #skF_7 > #skF_3 > #skF_14 > #skF_10 > #skF_6 > #skF_13 > #skF_8 > #skF_11 > #skF_2 > #skF_12 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_9',type,(
    '#skF_9': $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_13',type,(
    '#skF_13': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_289,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | v1_partfun1(C,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_funct_2)).

tff(f_215,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_267,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_271,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_107,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_201,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_121,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(c_166,plain,
    ( k1_xboole_0 = '#skF_13'
    | k1_xboole_0 != '#skF_14' ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_188,plain,(
    k1_xboole_0 != '#skF_14' ),
    inference(splitLeft,[status(thm)],[c_166])).

tff(c_174,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1(k2_zfmisc_1('#skF_13','#skF_14'))) ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_1516,plain,(
    ! [C_198,B_199,A_200] :
      ( v1_xboole_0(C_198)
      | ~ m1_subset_1(C_198,k1_zfmisc_1(k2_zfmisc_1(B_199,A_200)))
      | ~ v1_xboole_0(A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_1547,plain,
    ( v1_xboole_0('#skF_15')
    | ~ v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_174,c_1516])).

tff(c_3758,plain,(
    ~ v1_xboole_0('#skF_14') ),
    inference(splitLeft,[status(thm)],[c_1547])).

tff(c_164,plain,(
    ~ v1_partfun1('#skF_15','#skF_13') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_176,plain,(
    v1_funct_1('#skF_15') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_170,plain,(
    v1_funct_2('#skF_15','#skF_13','#skF_14') ),
    inference(cnfTransformation,[status(thm)],[f_289])).

tff(c_6159,plain,(
    ! [C_471,A_472,B_473] :
      ( v1_partfun1(C_471,A_472)
      | ~ v1_funct_2(C_471,A_472,B_473)
      | ~ v1_funct_1(C_471)
      | ~ m1_subset_1(C_471,k1_zfmisc_1(k2_zfmisc_1(A_472,B_473)))
      | v1_xboole_0(B_473) ) ),
    inference(cnfTransformation,[status(thm)],[f_267])).

tff(c_6203,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | ~ v1_funct_2('#skF_15','#skF_13','#skF_14')
    | ~ v1_funct_1('#skF_15')
    | v1_xboole_0('#skF_14') ),
    inference(resolution,[status(thm)],[c_174,c_6159])).

tff(c_6220,plain,
    ( v1_partfun1('#skF_15','#skF_13')
    | v1_xboole_0('#skF_14') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_170,c_6203])).

tff(c_6222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3758,c_164,c_6220])).

tff(c_6224,plain,(
    v1_xboole_0('#skF_14') ),
    inference(splitRight,[status(thm)],[c_1547])).

tff(c_16,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6231,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(resolution,[status(thm)],[c_6224,c_16])).

tff(c_6235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_6231])).

tff(c_6236,plain,(
    k1_xboole_0 = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_22,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6280,plain,(
    ! [B_9] : k2_zfmisc_1('#skF_13',B_9) = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_22])).

tff(c_6505,plain,(
    ! [A_508] : m1_subset_1(k6_partfun1(A_508),k1_zfmisc_1(k2_zfmisc_1(A_508,A_508))) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_48,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6549,plain,(
    ! [A_513] : r1_tarski(k6_partfun1(A_513),k2_zfmisc_1(A_513,A_513)) ),
    inference(resolution,[status(thm)],[c_6505,c_48])).

tff(c_6556,plain,(
    r1_tarski(k6_partfun1('#skF_13'),'#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_6280,c_6549])).

tff(c_20,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6263,plain,(
    ! [A_8] : k2_zfmisc_1(A_8,'#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_20])).

tff(c_26,plain,(
    ! [A_10,B_11] :
      ( ~ r1_tarski(A_10,k2_zfmisc_1(A_10,B_11))
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6432,plain,(
    ! [A_499,B_500] :
      ( ~ r1_tarski(A_499,k2_zfmisc_1(A_499,B_500))
      | A_499 = '#skF_13' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_26])).

tff(c_6438,plain,(
    ! [A_8] :
      ( ~ r1_tarski(A_8,'#skF_13')
      | A_8 = '#skF_13' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6263,c_6432])).

tff(c_6569,plain,(
    k6_partfun1('#skF_13') = '#skF_13' ),
    inference(resolution,[status(thm)],[c_6556,c_6438])).

tff(c_160,plain,(
    ! [A_90] : v1_partfun1(k6_partfun1(A_90),A_90) ),
    inference(cnfTransformation,[status(thm)],[f_271])).

tff(c_6583,plain,(
    v1_partfun1('#skF_13','#skF_13') ),
    inference(superposition,[status(thm),theory(equality)],[c_6569,c_160])).

tff(c_58,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6239,plain,(
    k2_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_58])).

tff(c_60,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_6238,plain,(
    k1_relat_1('#skF_13') = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_60])).

tff(c_32,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6274,plain,(
    k1_zfmisc_1('#skF_13') = k1_tarski('#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_32])).

tff(c_6237,plain,(
    k1_xboole_0 = '#skF_14' ),
    inference(splitRight,[status(thm)],[c_166])).

tff(c_6244,plain,(
    '#skF_14' = '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6237])).

tff(c_6273,plain,(
    m1_subset_1('#skF_15',k1_zfmisc_1('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6263,c_6244,c_174])).

tff(c_6275,plain,(
    m1_subset_1('#skF_15',k1_tarski('#skF_13')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_6273])).

tff(c_6454,plain,(
    ! [A_502,B_503] :
      ( r1_tarski(A_502,B_503)
      | ~ m1_subset_1(A_502,k1_zfmisc_1(B_503)) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_7085,plain,(
    ! [A_551] :
      ( r1_tarski(A_551,'#skF_13')
      | ~ m1_subset_1(A_551,k1_tarski('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6274,c_6454])).

tff(c_7098,plain,(
    r1_tarski('#skF_15','#skF_13') ),
    inference(resolution,[status(thm)],[c_6275,c_7085])).

tff(c_7140,plain,(
    '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_7098,c_6438])).

tff(c_6805,plain,(
    ! [C_528,A_529,B_530] :
      ( v1_relat_1(C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1(k2_zfmisc_1(A_529,B_530))) ) ),
    inference(cnfTransformation,[status(thm)],[f_201])).

tff(c_6820,plain,(
    ! [C_528] :
      ( v1_relat_1(C_528)
      | ~ m1_subset_1(C_528,k1_zfmisc_1('#skF_13')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6263,c_6805])).

tff(c_6943,plain,(
    ! [C_542] :
      ( v1_relat_1(C_542)
      | ~ m1_subset_1(C_542,k1_tarski('#skF_13')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6274,c_6820])).

tff(c_6952,plain,(
    v1_relat_1('#skF_15') ),
    inference(resolution,[status(thm)],[c_6275,c_6943])).

tff(c_68,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6692,plain,(
    ! [A_34] :
      ( k1_relat_1(A_34) != '#skF_13'
      | A_34 = '#skF_13'
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_68])).

tff(c_6971,plain,
    ( k1_relat_1('#skF_15') != '#skF_13'
    | '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_6952,c_6692])).

tff(c_7005,plain,(
    k1_relat_1('#skF_15') != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_6971])).

tff(c_7142,plain,(
    k1_relat_1('#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7140,c_7005])).

tff(c_7156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6238,c_7142])).

tff(c_7157,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_6971])).

tff(c_66,plain,(
    ! [A_34] :
      ( k2_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_6636,plain,(
    ! [A_34] :
      ( k2_relat_1(A_34) != '#skF_13'
      | A_34 = '#skF_13'
      | ~ v1_relat_1(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6236,c_6236,c_66])).

tff(c_6972,plain,
    ( k2_relat_1('#skF_15') != '#skF_13'
    | '#skF_15' = '#skF_13' ),
    inference(resolution,[status(thm)],[c_6952,c_6636])).

tff(c_6993,plain,(
    k2_relat_1('#skF_15') != '#skF_13' ),
    inference(splitLeft,[status(thm)],[c_6972])).

tff(c_7159,plain,(
    k2_relat_1('#skF_13') != '#skF_13' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7157,c_6993])).

tff(c_7171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6239,c_7159])).

tff(c_7172,plain,(
    '#skF_15' = '#skF_13' ),
    inference(splitRight,[status(thm)],[c_6972])).

tff(c_7182,plain,(
    ~ v1_partfun1('#skF_13','#skF_13') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7172,c_164])).

tff(c_7192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6583,c_7182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n011.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:55:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.38/2.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.50  
% 7.38/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.38/2.50  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k1_funct_1 > #nlpp > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_9 > #skF_5 > #skF_4 > #skF_15 > #skF_7 > #skF_3 > #skF_14 > #skF_10 > #skF_6 > #skF_13 > #skF_8 > #skF_11 > #skF_2 > #skF_12 > #skF_1
% 7.38/2.50  
% 7.38/2.50  %Foreground sorts:
% 7.38/2.50  
% 7.38/2.50  
% 7.38/2.50  %Background operators:
% 7.38/2.50  
% 7.38/2.50  
% 7.38/2.50  %Foreground operators:
% 7.38/2.50  tff('#skF_9', type, '#skF_9': $i > $i).
% 7.38/2.50  tff('#skF_5', type, '#skF_5': $i > $i).
% 7.38/2.50  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.38/2.50  tff('#skF_4', type, '#skF_4': $i > $i).
% 7.38/2.50  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 7.38/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.38/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.38/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.38/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.38/2.50  tff('#skF_15', type, '#skF_15': $i).
% 7.38/2.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 7.38/2.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.38/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.38/2.50  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 7.38/2.50  tff('#skF_7', type, '#skF_7': $i).
% 7.38/2.50  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.38/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.38/2.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.38/2.50  tff('#skF_14', type, '#skF_14': $i).
% 7.38/2.50  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.38/2.50  tff('#skF_10', type, '#skF_10': $i > $i).
% 7.38/2.50  tff('#skF_6', type, '#skF_6': $i).
% 7.38/2.50  tff('#skF_13', type, '#skF_13': $i).
% 7.38/2.50  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 7.38/2.50  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 7.38/2.50  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.38/2.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.38/2.50  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 7.38/2.50  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 7.38/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.38/2.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.38/2.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.38/2.50  tff('#skF_11', type, '#skF_11': $i > $i).
% 7.38/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.38/2.50  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.38/2.50  tff('#skF_12', type, '#skF_12': $i > $i).
% 7.38/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.38/2.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.38/2.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.38/2.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 7.38/2.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.38/2.50  
% 7.77/2.52  tff(f_289, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_funct_2)).
% 7.77/2.52  tff(f_215, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc4_relset_1)).
% 7.77/2.52  tff(f_267, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 7.77/2.52  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 7.77/2.52  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 7.77/2.52  tff(f_271, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 7.77/2.52  tff(f_90, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.77/2.52  tff(f_54, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 7.77/2.52  tff(f_107, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 7.77/2.52  tff(f_64, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 7.77/2.52  tff(f_201, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 7.77/2.52  tff(f_121, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 7.77/2.52  tff(c_166, plain, (k1_xboole_0='#skF_13' | k1_xboole_0!='#skF_14'), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.77/2.52  tff(c_188, plain, (k1_xboole_0!='#skF_14'), inference(splitLeft, [status(thm)], [c_166])).
% 7.77/2.52  tff(c_174, plain, (m1_subset_1('#skF_15', k1_zfmisc_1(k2_zfmisc_1('#skF_13', '#skF_14')))), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.77/2.52  tff(c_1516, plain, (![C_198, B_199, A_200]: (v1_xboole_0(C_198) | ~m1_subset_1(C_198, k1_zfmisc_1(k2_zfmisc_1(B_199, A_200))) | ~v1_xboole_0(A_200))), inference(cnfTransformation, [status(thm)], [f_215])).
% 7.77/2.52  tff(c_1547, plain, (v1_xboole_0('#skF_15') | ~v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_174, c_1516])).
% 7.77/2.52  tff(c_3758, plain, (~v1_xboole_0('#skF_14')), inference(splitLeft, [status(thm)], [c_1547])).
% 7.77/2.52  tff(c_164, plain, (~v1_partfun1('#skF_15', '#skF_13')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.77/2.52  tff(c_176, plain, (v1_funct_1('#skF_15')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.77/2.52  tff(c_170, plain, (v1_funct_2('#skF_15', '#skF_13', '#skF_14')), inference(cnfTransformation, [status(thm)], [f_289])).
% 7.77/2.52  tff(c_6159, plain, (![C_471, A_472, B_473]: (v1_partfun1(C_471, A_472) | ~v1_funct_2(C_471, A_472, B_473) | ~v1_funct_1(C_471) | ~m1_subset_1(C_471, k1_zfmisc_1(k2_zfmisc_1(A_472, B_473))) | v1_xboole_0(B_473))), inference(cnfTransformation, [status(thm)], [f_267])).
% 7.77/2.52  tff(c_6203, plain, (v1_partfun1('#skF_15', '#skF_13') | ~v1_funct_2('#skF_15', '#skF_13', '#skF_14') | ~v1_funct_1('#skF_15') | v1_xboole_0('#skF_14')), inference(resolution, [status(thm)], [c_174, c_6159])).
% 7.77/2.52  tff(c_6220, plain, (v1_partfun1('#skF_15', '#skF_13') | v1_xboole_0('#skF_14')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_170, c_6203])).
% 7.77/2.52  tff(c_6222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3758, c_164, c_6220])).
% 7.77/2.52  tff(c_6224, plain, (v1_xboole_0('#skF_14')), inference(splitRight, [status(thm)], [c_1547])).
% 7.77/2.52  tff(c_16, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_42])).
% 7.77/2.52  tff(c_6231, plain, (k1_xboole_0='#skF_14'), inference(resolution, [status(thm)], [c_6224, c_16])).
% 7.77/2.52  tff(c_6235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_188, c_6231])).
% 7.77/2.52  tff(c_6236, plain, (k1_xboole_0='#skF_13'), inference(splitRight, [status(thm)], [c_166])).
% 7.77/2.52  tff(c_22, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.77/2.52  tff(c_6280, plain, (![B_9]: (k2_zfmisc_1('#skF_13', B_9)='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_22])).
% 7.77/2.52  tff(c_6505, plain, (![A_508]: (m1_subset_1(k6_partfun1(A_508), k1_zfmisc_1(k2_zfmisc_1(A_508, A_508))))), inference(cnfTransformation, [status(thm)], [f_271])).
% 7.77/2.52  tff(c_48, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | ~m1_subset_1(A_26, k1_zfmisc_1(B_27)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.77/2.52  tff(c_6549, plain, (![A_513]: (r1_tarski(k6_partfun1(A_513), k2_zfmisc_1(A_513, A_513)))), inference(resolution, [status(thm)], [c_6505, c_48])).
% 7.77/2.52  tff(c_6556, plain, (r1_tarski(k6_partfun1('#skF_13'), '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_6280, c_6549])).
% 7.77/2.52  tff(c_20, plain, (![A_8]: (k2_zfmisc_1(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.77/2.52  tff(c_6263, plain, (![A_8]: (k2_zfmisc_1(A_8, '#skF_13')='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_20])).
% 7.77/2.52  tff(c_26, plain, (![A_10, B_11]: (~r1_tarski(A_10, k2_zfmisc_1(A_10, B_11)) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_54])).
% 7.77/2.52  tff(c_6432, plain, (![A_499, B_500]: (~r1_tarski(A_499, k2_zfmisc_1(A_499, B_500)) | A_499='#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_26])).
% 7.77/2.52  tff(c_6438, plain, (![A_8]: (~r1_tarski(A_8, '#skF_13') | A_8='#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_6263, c_6432])).
% 7.77/2.52  tff(c_6569, plain, (k6_partfun1('#skF_13')='#skF_13'), inference(resolution, [status(thm)], [c_6556, c_6438])).
% 7.77/2.52  tff(c_160, plain, (![A_90]: (v1_partfun1(k6_partfun1(A_90), A_90))), inference(cnfTransformation, [status(thm)], [f_271])).
% 7.77/2.52  tff(c_6583, plain, (v1_partfun1('#skF_13', '#skF_13')), inference(superposition, [status(thm), theory('equality')], [c_6569, c_160])).
% 7.77/2.52  tff(c_58, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.77/2.52  tff(c_6239, plain, (k2_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_58])).
% 7.77/2.52  tff(c_60, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_107])).
% 7.77/2.52  tff(c_6238, plain, (k1_relat_1('#skF_13')='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_60])).
% 7.77/2.52  tff(c_32, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.77/2.52  tff(c_6274, plain, (k1_zfmisc_1('#skF_13')=k1_tarski('#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_32])).
% 7.77/2.52  tff(c_6237, plain, (k1_xboole_0='#skF_14'), inference(splitRight, [status(thm)], [c_166])).
% 7.77/2.52  tff(c_6244, plain, ('#skF_14'='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6237])).
% 7.77/2.52  tff(c_6273, plain, (m1_subset_1('#skF_15', k1_zfmisc_1('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_6263, c_6244, c_174])).
% 7.77/2.52  tff(c_6275, plain, (m1_subset_1('#skF_15', k1_tarski('#skF_13'))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_6273])).
% 7.77/2.52  tff(c_6454, plain, (![A_502, B_503]: (r1_tarski(A_502, B_503) | ~m1_subset_1(A_502, k1_zfmisc_1(B_503)))), inference(cnfTransformation, [status(thm)], [f_90])).
% 7.77/2.52  tff(c_7085, plain, (![A_551]: (r1_tarski(A_551, '#skF_13') | ~m1_subset_1(A_551, k1_tarski('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_6274, c_6454])).
% 7.77/2.52  tff(c_7098, plain, (r1_tarski('#skF_15', '#skF_13')), inference(resolution, [status(thm)], [c_6275, c_7085])).
% 7.77/2.52  tff(c_7140, plain, ('#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_7098, c_6438])).
% 7.77/2.52  tff(c_6805, plain, (![C_528, A_529, B_530]: (v1_relat_1(C_528) | ~m1_subset_1(C_528, k1_zfmisc_1(k2_zfmisc_1(A_529, B_530))))), inference(cnfTransformation, [status(thm)], [f_201])).
% 7.77/2.52  tff(c_6820, plain, (![C_528]: (v1_relat_1(C_528) | ~m1_subset_1(C_528, k1_zfmisc_1('#skF_13')))), inference(superposition, [status(thm), theory('equality')], [c_6263, c_6805])).
% 7.77/2.52  tff(c_6943, plain, (![C_542]: (v1_relat_1(C_542) | ~m1_subset_1(C_542, k1_tarski('#skF_13')))), inference(demodulation, [status(thm), theory('equality')], [c_6274, c_6820])).
% 7.77/2.52  tff(c_6952, plain, (v1_relat_1('#skF_15')), inference(resolution, [status(thm)], [c_6275, c_6943])).
% 7.77/2.52  tff(c_68, plain, (![A_34]: (k1_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.77/2.52  tff(c_6692, plain, (![A_34]: (k1_relat_1(A_34)!='#skF_13' | A_34='#skF_13' | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_68])).
% 7.77/2.52  tff(c_6971, plain, (k1_relat_1('#skF_15')!='#skF_13' | '#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_6952, c_6692])).
% 7.77/2.52  tff(c_7005, plain, (k1_relat_1('#skF_15')!='#skF_13'), inference(splitLeft, [status(thm)], [c_6971])).
% 7.77/2.52  tff(c_7142, plain, (k1_relat_1('#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7140, c_7005])).
% 7.77/2.52  tff(c_7156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6238, c_7142])).
% 7.77/2.52  tff(c_7157, plain, ('#skF_15'='#skF_13'), inference(splitRight, [status(thm)], [c_6971])).
% 7.77/2.52  tff(c_66, plain, (![A_34]: (k2_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_121])).
% 7.77/2.52  tff(c_6636, plain, (![A_34]: (k2_relat_1(A_34)!='#skF_13' | A_34='#skF_13' | ~v1_relat_1(A_34))), inference(demodulation, [status(thm), theory('equality')], [c_6236, c_6236, c_66])).
% 7.77/2.52  tff(c_6972, plain, (k2_relat_1('#skF_15')!='#skF_13' | '#skF_15'='#skF_13'), inference(resolution, [status(thm)], [c_6952, c_6636])).
% 7.77/2.52  tff(c_6993, plain, (k2_relat_1('#skF_15')!='#skF_13'), inference(splitLeft, [status(thm)], [c_6972])).
% 7.77/2.52  tff(c_7159, plain, (k2_relat_1('#skF_13')!='#skF_13'), inference(demodulation, [status(thm), theory('equality')], [c_7157, c_6993])).
% 7.77/2.52  tff(c_7171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6239, c_7159])).
% 7.77/2.52  tff(c_7172, plain, ('#skF_15'='#skF_13'), inference(splitRight, [status(thm)], [c_6972])).
% 7.77/2.52  tff(c_7182, plain, (~v1_partfun1('#skF_13', '#skF_13')), inference(demodulation, [status(thm), theory('equality')], [c_7172, c_164])).
% 7.77/2.52  tff(c_7192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6583, c_7182])).
% 7.77/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.77/2.52  
% 7.77/2.52  Inference rules
% 7.77/2.52  ----------------------
% 7.77/2.52  #Ref     : 0
% 7.77/2.52  #Sup     : 1601
% 7.77/2.52  #Fact    : 0
% 7.77/2.52  #Define  : 0
% 7.77/2.52  #Split   : 29
% 7.77/2.52  #Chain   : 0
% 7.77/2.52  #Close   : 0
% 7.77/2.52  
% 7.77/2.52  Ordering : KBO
% 7.77/2.52  
% 7.77/2.52  Simplification rules
% 7.77/2.52  ----------------------
% 7.77/2.52  #Subsume      : 234
% 7.77/2.52  #Demod        : 621
% 7.77/2.52  #Tautology    : 756
% 7.77/2.52  #SimpNegUnit  : 45
% 7.77/2.52  #BackRed      : 68
% 7.77/2.52  
% 7.77/2.52  #Partial instantiations: 0
% 7.77/2.52  #Strategies tried      : 1
% 7.77/2.52  
% 7.77/2.52  Timing (in seconds)
% 7.77/2.52  ----------------------
% 7.77/2.52  Preprocessing        : 0.41
% 7.77/2.52  Parsing              : 0.20
% 7.77/2.52  CNF conversion       : 0.04
% 7.77/2.52  Main loop            : 1.34
% 7.77/2.52  Inferencing          : 0.44
% 7.77/2.52  Reduction            : 0.46
% 7.77/2.52  Demodulation         : 0.32
% 7.77/2.52  BG Simplification    : 0.05
% 7.77/2.52  Subsumption          : 0.27
% 7.77/2.52  Abstraction          : 0.05
% 7.77/2.52  MUC search           : 0.00
% 7.77/2.52  Cooper               : 0.00
% 7.77/2.52  Total                : 1.79
% 7.77/2.52  Index Insertion      : 0.00
% 7.77/2.52  Index Deletion       : 0.00
% 7.77/2.52  Index Matching       : 0.00
% 7.77/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
