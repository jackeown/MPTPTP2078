%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:40 EST 2020

% Result     : Theorem 16.85s
% Output     : CNFRefutation 16.85s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 202 expanded)
%              Number of leaves         :   82 ( 118 expanded)
%              Depth                    :    8
%              Number of atoms          :  158 ( 379 expanded)
%              Number of equality atoms :  107 ( 285 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_23 > #skF_33 > #skF_28 > #skF_22 > #skF_21 > #skF_16 > #skF_6 > #skF_34 > #skF_1 > #skF_18 > #skF_25 > #skF_19 > #skF_38 > #skF_36 > #skF_37 > #skF_3 > #skF_14 > #skF_24 > #skF_32 > #skF_31 > #skF_29 > #skF_10 > #skF_2 > #skF_8 > #skF_15 > #skF_13 > #skF_17 > #skF_11 > #skF_35 > #skF_12 > #skF_7 > #skF_26 > #skF_9 > #skF_5 > #skF_30 > #skF_27 > #skF_4 > #skF_20

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_23',type,(
    '#skF_23': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_33',type,(
    '#skF_33': ( $i * $i * $i * $i ) > $i )).

tff('#skF_28',type,(
    '#skF_28': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_22',type,(
    '#skF_22': ( $i * $i ) > $i )).

tff('#skF_21',type,(
    '#skF_21': $i > $i )).

tff('#skF_16',type,(
    '#skF_16': $i > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_34',type,(
    '#skF_34': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#skF_18',type,(
    '#skF_18': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_25',type,(
    '#skF_25': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_19',type,(
    '#skF_19': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_38',type,(
    '#skF_38': $i )).

tff('#skF_36',type,(
    '#skF_36': $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff('#skF_37',type,(
    '#skF_37': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_14',type,(
    '#skF_14': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_24',type,(
    '#skF_24': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_32',type,(
    '#skF_32': ( $i * $i * $i * $i ) > $i )).

tff('#skF_31',type,(
    '#skF_31': ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_29',type,(
    '#skF_29': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_15',type,(
    '#skF_15': ( $i * $i * $i ) > $i )).

tff('#skF_13',type,(
    '#skF_13': $i > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_17',type,(
    '#skF_17': $i > $i )).

tff('#skF_11',type,(
    '#skF_11': $i > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_35',type,(
    '#skF_35': $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_12',type,(
    '#skF_12': $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_26',type,(
    '#skF_26': ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_30',type,(
    '#skF_30': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_27',type,(
    '#skF_27': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff('#skF_20',type,(
    '#skF_20': $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_663,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ~ ! [D] :
                ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
               => ( D != k5_mcart_1(A,B,C,D)
                  & D != k6_mcart_1(A,B,C,D)
                  & D != k7_mcart_1(A,B,C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_mcart_1)).

tff(f_639,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_99,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_607,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_585,axiom,(
    ! [A,B,C] : k3_zfmisc_1(k1_tarski(A),k1_tarski(B),k1_tarski(C)) = k1_tarski(k3_mcart_1(A,B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_mcart_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_180,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_237,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_272,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_619,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_tarski(A,k3_zfmisc_1(A,B,C))
          & ~ r1_tarski(A,k3_zfmisc_1(B,C,A))
          & ~ r1_tarski(A,k3_zfmisc_1(C,A,B)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_mcart_1)).

tff(c_38,plain,(
    ! [B_15] : r1_tarski(B_15,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_368,plain,(
    k1_xboole_0 != '#skF_35' ),
    inference(cnfTransformation,[status(thm)],[f_663])).

tff(c_366,plain,(
    k1_xboole_0 != '#skF_36' ),
    inference(cnfTransformation,[status(thm)],[f_663])).

tff(c_364,plain,(
    k1_xboole_0 != '#skF_37' ),
    inference(cnfTransformation,[status(thm)],[f_663])).

tff(c_362,plain,(
    m1_subset_1('#skF_38',k3_zfmisc_1('#skF_35','#skF_36','#skF_37')) ),
    inference(cnfTransformation,[status(thm)],[f_663])).

tff(c_39354,plain,(
    ! [A_2555,B_2556,C_2557,D_2558] :
      ( k7_mcart_1(A_2555,B_2556,C_2557,D_2558) = k2_mcart_1(D_2558)
      | ~ m1_subset_1(D_2558,k3_zfmisc_1(A_2555,B_2556,C_2557))
      | k1_xboole_0 = C_2557
      | k1_xboole_0 = B_2556
      | k1_xboole_0 = A_2555 ) ),
    inference(cnfTransformation,[status(thm)],[f_639])).

tff(c_39430,plain,
    ( k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = k2_mcart_1('#skF_38')
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(resolution,[status(thm)],[c_362,c_39354])).

tff(c_39453,plain,(
    k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = k2_mcart_1('#skF_38') ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_366,c_364,c_39430])).

tff(c_68,plain,(
    ! [C_39] : r2_hidden(C_39,k1_tarski(C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_10672,plain,(
    ! [A_1034,B_1035,C_1036,D_1037] :
      ( k7_mcart_1(A_1034,B_1035,C_1036,D_1037) = k2_mcart_1(D_1037)
      | ~ m1_subset_1(D_1037,k3_zfmisc_1(A_1034,B_1035,C_1036))
      | k1_xboole_0 = C_1036
      | k1_xboole_0 = B_1035
      | k1_xboole_0 = A_1034 ) ),
    inference(cnfTransformation,[status(thm)],[f_639])).

tff(c_10740,plain,
    ( k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = k2_mcart_1('#skF_38')
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(resolution,[status(thm)],[c_362,c_10672])).

tff(c_10761,plain,(
    k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = k2_mcart_1('#skF_38') ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_366,c_364,c_10740])).

tff(c_360,plain,
    ( k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38'
    | k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38'
    | k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38' ),
    inference(cnfTransformation,[status(thm)],[f_663])).

tff(c_396,plain,(
    k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38' ),
    inference(splitLeft,[status(thm)],[c_360])).

tff(c_13304,plain,(
    ! [A_1145,B_1146,C_1147,D_1148] :
      ( k3_mcart_1(k5_mcart_1(A_1145,B_1146,C_1147,D_1148),k6_mcart_1(A_1145,B_1146,C_1147,D_1148),k7_mcart_1(A_1145,B_1146,C_1147,D_1148)) = D_1148
      | ~ m1_subset_1(D_1148,k3_zfmisc_1(A_1145,B_1146,C_1147))
      | k1_xboole_0 = C_1147
      | k1_xboole_0 = B_1146
      | k1_xboole_0 = A_1145 ) ),
    inference(cnfTransformation,[status(thm)],[f_607])).

tff(c_13352,plain,
    ( k3_mcart_1('#skF_38',k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38')) = '#skF_38'
    | ~ m1_subset_1('#skF_38',k3_zfmisc_1('#skF_35','#skF_36','#skF_37'))
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_13304])).

tff(c_13359,plain,
    ( k3_mcart_1('#skF_38',k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k2_mcart_1('#skF_38')) = '#skF_38'
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_10761,c_13352])).

tff(c_13360,plain,(
    k3_mcart_1('#skF_38',k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k2_mcart_1('#skF_38')) = '#skF_38' ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_366,c_364,c_13359])).

tff(c_6600,plain,(
    ! [A_848,B_849,C_850] : k3_zfmisc_1(k1_tarski(A_848),k1_tarski(B_849),k1_tarski(C_850)) = k1_tarski(k3_mcart_1(A_848,B_849,C_850)) ),
    inference(cnfTransformation,[status(thm)],[f_585])).

tff(c_24,plain,(
    ! [A_9] : k2_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_594,plain,(
    ! [A_454,B_455] : k2_xboole_0(k1_tarski(A_454),B_455) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_598,plain,(
    ! [A_454] : k1_tarski(A_454) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_594])).

tff(c_2004,plain,(
    ! [A_571,B_572] :
      ( m1_subset_1(k1_tarski(A_571),k1_zfmisc_1(B_572))
      | ~ r2_hidden(A_571,B_572) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_184,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(A_101,B_102)
      | ~ m1_subset_1(A_101,k1_zfmisc_1(B_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_272])).

tff(c_2505,plain,(
    ! [A_604,B_605] :
      ( r1_tarski(k1_tarski(A_604),B_605)
      | ~ r2_hidden(A_604,B_605) ) ),
    inference(resolution,[status(thm)],[c_2004,c_184])).

tff(c_352,plain,(
    ! [A_409,B_410,C_411] :
      ( ~ r1_tarski(A_409,k3_zfmisc_1(A_409,B_410,C_411))
      | k1_xboole_0 = A_409 ) ),
    inference(cnfTransformation,[status(thm)],[f_619])).

tff(c_2520,plain,(
    ! [A_604,B_410,C_411] :
      ( k1_tarski(A_604) = k1_xboole_0
      | ~ r2_hidden(A_604,k3_zfmisc_1(k1_tarski(A_604),B_410,C_411)) ) ),
    inference(resolution,[status(thm)],[c_2505,c_352])).

tff(c_2546,plain,(
    ! [A_604,B_410,C_411] : ~ r2_hidden(A_604,k3_zfmisc_1(k1_tarski(A_604),B_410,C_411)) ),
    inference(negUnitSimplification,[status(thm)],[c_598,c_2520])).

tff(c_6611,plain,(
    ! [A_848,B_849,C_850] : ~ r2_hidden(A_848,k1_tarski(k3_mcart_1(A_848,B_849,C_850))) ),
    inference(superposition,[status(thm),theory(equality)],[c_6600,c_2546])).

tff(c_13688,plain,(
    ~ r2_hidden('#skF_38',k1_tarski('#skF_38')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13360,c_6611])).

tff(c_13702,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_13688])).

tff(c_13703,plain,
    ( k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38'
    | k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38' ),
    inference(splitRight,[status(thm)],[c_360])).

tff(c_13822,plain,(
    k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38' ),
    inference(splitLeft,[status(thm)],[c_13703])).

tff(c_28182,plain,(
    ! [A_1909,B_1910,C_1911,D_1912] :
      ( k3_mcart_1(k5_mcart_1(A_1909,B_1910,C_1911,D_1912),k6_mcart_1(A_1909,B_1910,C_1911,D_1912),k7_mcart_1(A_1909,B_1910,C_1911,D_1912)) = D_1912
      | ~ m1_subset_1(D_1912,k3_zfmisc_1(A_1909,B_1910,C_1911))
      | k1_xboole_0 = C_1911
      | k1_xboole_0 = B_1910
      | k1_xboole_0 = A_1909 ) ),
    inference(cnfTransformation,[status(thm)],[f_607])).

tff(c_28224,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38') = '#skF_38'
    | ~ m1_subset_1('#skF_38',k3_zfmisc_1('#skF_35','#skF_36','#skF_37'))
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(superposition,[status(thm),theory(equality)],[c_13822,c_28182])).

tff(c_28228,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38') = '#skF_38'
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_28224])).

tff(c_28229,plain,(
    k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38') = '#skF_38' ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_366,c_364,c_28228])).

tff(c_19463,plain,(
    ! [A_1575,B_1576,C_1577] : k3_zfmisc_1(k1_tarski(A_1575),k1_tarski(B_1576),k1_tarski(C_1577)) = k1_tarski(k3_mcart_1(A_1575,B_1576,C_1577)) ),
    inference(cnfTransformation,[status(thm)],[f_585])).

tff(c_13900,plain,(
    ! [A_1190,B_1191] : k2_xboole_0(k1_tarski(A_1190),B_1191) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_13904,plain,(
    ! [A_1190] : k1_tarski(A_1190) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_13900])).

tff(c_15963,plain,(
    ! [A_1340,B_1341] :
      ( m1_subset_1(k1_tarski(A_1340),k1_zfmisc_1(B_1341))
      | ~ r2_hidden(A_1340,B_1341) ) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_15984,plain,(
    ! [A_1340,B_1341] :
      ( r1_tarski(k1_tarski(A_1340),B_1341)
      | ~ r2_hidden(A_1340,B_1341) ) ),
    inference(resolution,[status(thm)],[c_15963,c_184])).

tff(c_16189,plain,(
    ! [A_1355,B_1356,C_1357] :
      ( ~ r1_tarski(A_1355,k3_zfmisc_1(B_1356,C_1357,A_1355))
      | k1_xboole_0 = A_1355 ) ),
    inference(cnfTransformation,[status(thm)],[f_619])).

tff(c_16193,plain,(
    ! [A_1340,B_1356,C_1357] :
      ( k1_tarski(A_1340) = k1_xboole_0
      | ~ r2_hidden(A_1340,k3_zfmisc_1(B_1356,C_1357,k1_tarski(A_1340))) ) ),
    inference(resolution,[status(thm)],[c_15984,c_16189])).

tff(c_16213,plain,(
    ! [A_1340,B_1356,C_1357] : ~ r2_hidden(A_1340,k3_zfmisc_1(B_1356,C_1357,k1_tarski(A_1340))) ),
    inference(negUnitSimplification,[status(thm)],[c_13904,c_16193])).

tff(c_19490,plain,(
    ! [C_1577,A_1575,B_1576] : ~ r2_hidden(C_1577,k1_tarski(k3_mcart_1(A_1575,B_1576,C_1577))) ),
    inference(superposition,[status(thm),theory(equality)],[c_19463,c_16213])).

tff(c_28415,plain,(
    ~ r2_hidden('#skF_38',k1_tarski('#skF_38')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28229,c_19490])).

tff(c_28423,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_28415])).

tff(c_28424,plain,(
    k6_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38') = '#skF_38' ),
    inference(splitRight,[status(thm)],[c_13703])).

tff(c_42313,plain,(
    ! [A_2637,B_2638,C_2639,D_2640] :
      ( k3_mcart_1(k5_mcart_1(A_2637,B_2638,C_2639,D_2640),k6_mcart_1(A_2637,B_2638,C_2639,D_2640),k7_mcart_1(A_2637,B_2638,C_2639,D_2640)) = D_2640
      | ~ m1_subset_1(D_2640,k3_zfmisc_1(A_2637,B_2638,C_2639))
      | k1_xboole_0 = C_2639
      | k1_xboole_0 = B_2638
      | k1_xboole_0 = A_2637 ) ),
    inference(cnfTransformation,[status(thm)],[f_607])).

tff(c_42361,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38',k7_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38')) = '#skF_38'
    | ~ m1_subset_1('#skF_38',k3_zfmisc_1('#skF_35','#skF_36','#skF_37'))
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(superposition,[status(thm),theory(equality)],[c_28424,c_42313])).

tff(c_42368,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38',k2_mcart_1('#skF_38')) = '#skF_38'
    | k1_xboole_0 = '#skF_37'
    | k1_xboole_0 = '#skF_36'
    | k1_xboole_0 = '#skF_35' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_39453,c_42361])).

tff(c_42369,plain,(
    k3_mcart_1(k5_mcart_1('#skF_35','#skF_36','#skF_37','#skF_38'),'#skF_38',k2_mcart_1('#skF_38')) = '#skF_38' ),
    inference(negUnitSimplification,[status(thm)],[c_368,c_366,c_364,c_42368])).

tff(c_28499,plain,(
    ! [A_1936,B_1937] : k2_xboole_0(k1_tarski(A_1936),B_1937) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_180])).

tff(c_28503,plain,(
    ! [A_1936] : k1_tarski(A_1936) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_28499])).

tff(c_34248,plain,(
    ! [A_2331,B_2332,C_2333] : k3_zfmisc_1(k1_tarski(A_2331),k1_tarski(B_2332),k1_tarski(C_2333)) = k1_tarski(k3_mcart_1(A_2331,B_2332,C_2333)) ),
    inference(cnfTransformation,[status(thm)],[f_585])).

tff(c_348,plain,(
    ! [A_409,C_411,B_410] :
      ( ~ r1_tarski(A_409,k3_zfmisc_1(C_411,A_409,B_410))
      | k1_xboole_0 = A_409 ) ),
    inference(cnfTransformation,[status(thm)],[f_619])).

tff(c_34284,plain,(
    ! [B_2332,A_2331,C_2333] :
      ( ~ r1_tarski(k1_tarski(B_2332),k1_tarski(k3_mcart_1(A_2331,B_2332,C_2333)))
      | k1_tarski(B_2332) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34248,c_348])).

tff(c_34297,plain,(
    ! [B_2332,A_2331,C_2333] : ~ r1_tarski(k1_tarski(B_2332),k1_tarski(k3_mcart_1(A_2331,B_2332,C_2333))) ),
    inference(negUnitSimplification,[status(thm)],[c_28503,c_34284])).

tff(c_42398,plain,(
    ~ r1_tarski(k1_tarski('#skF_38'),k1_tarski('#skF_38')) ),
    inference(superposition,[status(thm),theory(equality)],[c_42369,c_34297])).

tff(c_42424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42398])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:09:16 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.85/7.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/7.51  
% 16.85/7.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/7.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v3_ordinal1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k7_relat_1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k1_funct_1 > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k2_mcart_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_mcart_1 > k1_xboole_0 > #skF_23 > #skF_33 > #skF_28 > #skF_22 > #skF_21 > #skF_16 > #skF_6 > #skF_34 > #skF_1 > #skF_18 > #skF_25 > #skF_19 > #skF_38 > #skF_36 > #skF_37 > #skF_3 > #skF_14 > #skF_24 > #skF_32 > #skF_31 > #skF_29 > #skF_10 > #skF_2 > #skF_8 > #skF_15 > #skF_13 > #skF_17 > #skF_11 > #skF_35 > #skF_12 > #skF_7 > #skF_26 > #skF_9 > #skF_5 > #skF_30 > #skF_27 > #skF_4 > #skF_20
% 16.85/7.51  
% 16.85/7.51  %Foreground sorts:
% 16.85/7.51  
% 16.85/7.51  
% 16.85/7.51  %Background operators:
% 16.85/7.51  
% 16.85/7.51  
% 16.85/7.51  %Foreground operators:
% 16.85/7.51  tff('#skF_23', type, '#skF_23': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_33', type, '#skF_33': ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_28', type, '#skF_28': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_22', type, '#skF_22': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_21', type, '#skF_21': $i > $i).
% 16.85/7.51  tff('#skF_16', type, '#skF_16': $i > $i).
% 16.85/7.51  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_34', type, '#skF_34': ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 16.85/7.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.85/7.51  tff('#skF_18', type, '#skF_18': $i > $i).
% 16.85/7.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.85/7.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.85/7.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 16.85/7.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.85/7.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 16.85/7.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.85/7.51  tff('#skF_25', type, '#skF_25': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_19', type, '#skF_19': $i > $i).
% 16.85/7.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.85/7.51  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_38', type, '#skF_38': $i).
% 16.85/7.51  tff('#skF_36', type, '#skF_36': $i).
% 16.85/7.51  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 16.85/7.51  tff('#skF_37', type, '#skF_37': $i).
% 16.85/7.51  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 16.85/7.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.85/7.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.85/7.51  tff('#skF_14', type, '#skF_14': ($i * $i) > $i).
% 16.85/7.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.85/7.51  tff('#skF_24', type, '#skF_24': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_32', type, '#skF_32': ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_31', type, '#skF_31': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.85/7.51  tff('#skF_29', type, '#skF_29': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 16.85/7.51  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 16.85/7.51  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 16.85/7.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.85/7.51  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 16.85/7.51  tff('#skF_15', type, '#skF_15': ($i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_13', type, '#skF_13': $i > $i).
% 16.85/7.51  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.85/7.51  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 16.85/7.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 16.85/7.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.85/7.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.85/7.51  tff('#skF_17', type, '#skF_17': $i > $i).
% 16.85/7.51  tff('#skF_11', type, '#skF_11': $i > $i).
% 16.85/7.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 16.85/7.51  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.85/7.51  tff('#skF_35', type, '#skF_35': $i).
% 16.85/7.51  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 16.85/7.51  tff('#skF_12', type, '#skF_12': $i > $i).
% 16.85/7.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 16.85/7.51  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_26', type, '#skF_26': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.85/7.51  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_30', type, '#skF_30': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.85/7.51  tff('#skF_27', type, '#skF_27': ($i * $i * $i * $i * $i) > $i).
% 16.85/7.51  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.85/7.51  tff('#skF_20', type, '#skF_20': $i > $i).
% 16.85/7.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.85/7.51  
% 16.85/7.54  tff(f_52, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.85/7.54  tff(f_663, negated_conjecture, ~(![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ((~(D = k5_mcart_1(A, B, C, D)) & ~(D = k6_mcart_1(A, B, C, D))) & ~(D = k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_mcart_1)).
% 16.85/7.54  tff(f_639, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 16.85/7.54  tff(f_99, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 16.85/7.54  tff(f_607, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_mcart_1)).
% 16.85/7.54  tff(f_585, axiom, (![A, B, C]: (k3_zfmisc_1(k1_tarski(A), k1_tarski(B), k1_tarski(C)) = k1_tarski(k3_mcart_1(A, B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_mcart_1)).
% 16.85/7.54  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 16.85/7.54  tff(f_180, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 16.85/7.54  tff(f_237, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_subset_1)).
% 16.85/7.54  tff(f_272, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 16.85/7.54  tff(f_619, axiom, (![A, B, C]: (~((~r1_tarski(A, k3_zfmisc_1(A, B, C)) & ~r1_tarski(A, k3_zfmisc_1(B, C, A))) & ~r1_tarski(A, k3_zfmisc_1(C, A, B))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_mcart_1)).
% 16.85/7.54  tff(c_38, plain, (![B_15]: (r1_tarski(B_15, B_15))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.85/7.54  tff(c_368, plain, (k1_xboole_0!='#skF_35'), inference(cnfTransformation, [status(thm)], [f_663])).
% 16.85/7.54  tff(c_366, plain, (k1_xboole_0!='#skF_36'), inference(cnfTransformation, [status(thm)], [f_663])).
% 16.85/7.54  tff(c_364, plain, (k1_xboole_0!='#skF_37'), inference(cnfTransformation, [status(thm)], [f_663])).
% 16.85/7.54  tff(c_362, plain, (m1_subset_1('#skF_38', k3_zfmisc_1('#skF_35', '#skF_36', '#skF_37'))), inference(cnfTransformation, [status(thm)], [f_663])).
% 16.85/7.54  tff(c_39354, plain, (![A_2555, B_2556, C_2557, D_2558]: (k7_mcart_1(A_2555, B_2556, C_2557, D_2558)=k2_mcart_1(D_2558) | ~m1_subset_1(D_2558, k3_zfmisc_1(A_2555, B_2556, C_2557)) | k1_xboole_0=C_2557 | k1_xboole_0=B_2556 | k1_xboole_0=A_2555)), inference(cnfTransformation, [status(thm)], [f_639])).
% 16.85/7.54  tff(c_39430, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')=k2_mcart_1('#skF_38') | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(resolution, [status(thm)], [c_362, c_39354])).
% 16.85/7.54  tff(c_39453, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')=k2_mcart_1('#skF_38')), inference(negUnitSimplification, [status(thm)], [c_368, c_366, c_364, c_39430])).
% 16.85/7.54  tff(c_68, plain, (![C_39]: (r2_hidden(C_39, k1_tarski(C_39)))), inference(cnfTransformation, [status(thm)], [f_99])).
% 16.85/7.54  tff(c_10672, plain, (![A_1034, B_1035, C_1036, D_1037]: (k7_mcart_1(A_1034, B_1035, C_1036, D_1037)=k2_mcart_1(D_1037) | ~m1_subset_1(D_1037, k3_zfmisc_1(A_1034, B_1035, C_1036)) | k1_xboole_0=C_1036 | k1_xboole_0=B_1035 | k1_xboole_0=A_1034)), inference(cnfTransformation, [status(thm)], [f_639])).
% 16.85/7.54  tff(c_10740, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')=k2_mcart_1('#skF_38') | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(resolution, [status(thm)], [c_362, c_10672])).
% 16.85/7.54  tff(c_10761, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')=k2_mcart_1('#skF_38')), inference(negUnitSimplification, [status(thm)], [c_368, c_366, c_364, c_10740])).
% 16.85/7.54  tff(c_360, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38' | k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38' | k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38'), inference(cnfTransformation, [status(thm)], [f_663])).
% 16.85/7.54  tff(c_396, plain, (k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38'), inference(splitLeft, [status(thm)], [c_360])).
% 16.85/7.54  tff(c_13304, plain, (![A_1145, B_1146, C_1147, D_1148]: (k3_mcart_1(k5_mcart_1(A_1145, B_1146, C_1147, D_1148), k6_mcart_1(A_1145, B_1146, C_1147, D_1148), k7_mcart_1(A_1145, B_1146, C_1147, D_1148))=D_1148 | ~m1_subset_1(D_1148, k3_zfmisc_1(A_1145, B_1146, C_1147)) | k1_xboole_0=C_1147 | k1_xboole_0=B_1146 | k1_xboole_0=A_1145)), inference(cnfTransformation, [status(thm)], [f_607])).
% 16.85/7.54  tff(c_13352, plain, (k3_mcart_1('#skF_38', k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'))='#skF_38' | ~m1_subset_1('#skF_38', k3_zfmisc_1('#skF_35', '#skF_36', '#skF_37')) | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(superposition, [status(thm), theory('equality')], [c_396, c_13304])).
% 16.85/7.54  tff(c_13359, plain, (k3_mcart_1('#skF_38', k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k2_mcart_1('#skF_38'))='#skF_38' | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_10761, c_13352])).
% 16.85/7.54  tff(c_13360, plain, (k3_mcart_1('#skF_38', k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k2_mcart_1('#skF_38'))='#skF_38'), inference(negUnitSimplification, [status(thm)], [c_368, c_366, c_364, c_13359])).
% 16.85/7.54  tff(c_6600, plain, (![A_848, B_849, C_850]: (k3_zfmisc_1(k1_tarski(A_848), k1_tarski(B_849), k1_tarski(C_850))=k1_tarski(k3_mcart_1(A_848, B_849, C_850)))), inference(cnfTransformation, [status(thm)], [f_585])).
% 16.85/7.54  tff(c_24, plain, (![A_9]: (k2_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 16.85/7.54  tff(c_594, plain, (![A_454, B_455]: (k2_xboole_0(k1_tarski(A_454), B_455)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.85/7.54  tff(c_598, plain, (![A_454]: (k1_tarski(A_454)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_594])).
% 16.85/7.54  tff(c_2004, plain, (![A_571, B_572]: (m1_subset_1(k1_tarski(A_571), k1_zfmisc_1(B_572)) | ~r2_hidden(A_571, B_572))), inference(cnfTransformation, [status(thm)], [f_237])).
% 16.85/7.54  tff(c_184, plain, (![A_101, B_102]: (r1_tarski(A_101, B_102) | ~m1_subset_1(A_101, k1_zfmisc_1(B_102)))), inference(cnfTransformation, [status(thm)], [f_272])).
% 16.85/7.54  tff(c_2505, plain, (![A_604, B_605]: (r1_tarski(k1_tarski(A_604), B_605) | ~r2_hidden(A_604, B_605))), inference(resolution, [status(thm)], [c_2004, c_184])).
% 16.85/7.54  tff(c_352, plain, (![A_409, B_410, C_411]: (~r1_tarski(A_409, k3_zfmisc_1(A_409, B_410, C_411)) | k1_xboole_0=A_409)), inference(cnfTransformation, [status(thm)], [f_619])).
% 16.85/7.54  tff(c_2520, plain, (![A_604, B_410, C_411]: (k1_tarski(A_604)=k1_xboole_0 | ~r2_hidden(A_604, k3_zfmisc_1(k1_tarski(A_604), B_410, C_411)))), inference(resolution, [status(thm)], [c_2505, c_352])).
% 16.85/7.54  tff(c_2546, plain, (![A_604, B_410, C_411]: (~r2_hidden(A_604, k3_zfmisc_1(k1_tarski(A_604), B_410, C_411)))), inference(negUnitSimplification, [status(thm)], [c_598, c_2520])).
% 16.85/7.54  tff(c_6611, plain, (![A_848, B_849, C_850]: (~r2_hidden(A_848, k1_tarski(k3_mcart_1(A_848, B_849, C_850))))), inference(superposition, [status(thm), theory('equality')], [c_6600, c_2546])).
% 16.85/7.54  tff(c_13688, plain, (~r2_hidden('#skF_38', k1_tarski('#skF_38'))), inference(superposition, [status(thm), theory('equality')], [c_13360, c_6611])).
% 16.85/7.54  tff(c_13702, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_13688])).
% 16.85/7.54  tff(c_13703, plain, (k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38' | k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38'), inference(splitRight, [status(thm)], [c_360])).
% 16.85/7.54  tff(c_13822, plain, (k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38'), inference(splitLeft, [status(thm)], [c_13703])).
% 16.85/7.54  tff(c_28182, plain, (![A_1909, B_1910, C_1911, D_1912]: (k3_mcart_1(k5_mcart_1(A_1909, B_1910, C_1911, D_1912), k6_mcart_1(A_1909, B_1910, C_1911, D_1912), k7_mcart_1(A_1909, B_1910, C_1911, D_1912))=D_1912 | ~m1_subset_1(D_1912, k3_zfmisc_1(A_1909, B_1910, C_1911)) | k1_xboole_0=C_1911 | k1_xboole_0=B_1910 | k1_xboole_0=A_1909)), inference(cnfTransformation, [status(thm)], [f_607])).
% 16.85/7.54  tff(c_28224, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38')='#skF_38' | ~m1_subset_1('#skF_38', k3_zfmisc_1('#skF_35', '#skF_36', '#skF_37')) | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(superposition, [status(thm), theory('equality')], [c_13822, c_28182])).
% 16.85/7.54  tff(c_28228, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38')='#skF_38' | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_28224])).
% 16.85/7.54  tff(c_28229, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38')='#skF_38'), inference(negUnitSimplification, [status(thm)], [c_368, c_366, c_364, c_28228])).
% 16.85/7.54  tff(c_19463, plain, (![A_1575, B_1576, C_1577]: (k3_zfmisc_1(k1_tarski(A_1575), k1_tarski(B_1576), k1_tarski(C_1577))=k1_tarski(k3_mcart_1(A_1575, B_1576, C_1577)))), inference(cnfTransformation, [status(thm)], [f_585])).
% 16.85/7.54  tff(c_13900, plain, (![A_1190, B_1191]: (k2_xboole_0(k1_tarski(A_1190), B_1191)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.85/7.54  tff(c_13904, plain, (![A_1190]: (k1_tarski(A_1190)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_13900])).
% 16.85/7.54  tff(c_15963, plain, (![A_1340, B_1341]: (m1_subset_1(k1_tarski(A_1340), k1_zfmisc_1(B_1341)) | ~r2_hidden(A_1340, B_1341))), inference(cnfTransformation, [status(thm)], [f_237])).
% 16.85/7.54  tff(c_15984, plain, (![A_1340, B_1341]: (r1_tarski(k1_tarski(A_1340), B_1341) | ~r2_hidden(A_1340, B_1341))), inference(resolution, [status(thm)], [c_15963, c_184])).
% 16.85/7.54  tff(c_16189, plain, (![A_1355, B_1356, C_1357]: (~r1_tarski(A_1355, k3_zfmisc_1(B_1356, C_1357, A_1355)) | k1_xboole_0=A_1355)), inference(cnfTransformation, [status(thm)], [f_619])).
% 16.85/7.54  tff(c_16193, plain, (![A_1340, B_1356, C_1357]: (k1_tarski(A_1340)=k1_xboole_0 | ~r2_hidden(A_1340, k3_zfmisc_1(B_1356, C_1357, k1_tarski(A_1340))))), inference(resolution, [status(thm)], [c_15984, c_16189])).
% 16.85/7.54  tff(c_16213, plain, (![A_1340, B_1356, C_1357]: (~r2_hidden(A_1340, k3_zfmisc_1(B_1356, C_1357, k1_tarski(A_1340))))), inference(negUnitSimplification, [status(thm)], [c_13904, c_16193])).
% 16.85/7.54  tff(c_19490, plain, (![C_1577, A_1575, B_1576]: (~r2_hidden(C_1577, k1_tarski(k3_mcart_1(A_1575, B_1576, C_1577))))), inference(superposition, [status(thm), theory('equality')], [c_19463, c_16213])).
% 16.85/7.54  tff(c_28415, plain, (~r2_hidden('#skF_38', k1_tarski('#skF_38'))), inference(superposition, [status(thm), theory('equality')], [c_28229, c_19490])).
% 16.85/7.54  tff(c_28423, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_68, c_28415])).
% 16.85/7.54  tff(c_28424, plain, (k6_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38')='#skF_38'), inference(splitRight, [status(thm)], [c_13703])).
% 16.85/7.54  tff(c_42313, plain, (![A_2637, B_2638, C_2639, D_2640]: (k3_mcart_1(k5_mcart_1(A_2637, B_2638, C_2639, D_2640), k6_mcart_1(A_2637, B_2638, C_2639, D_2640), k7_mcart_1(A_2637, B_2638, C_2639, D_2640))=D_2640 | ~m1_subset_1(D_2640, k3_zfmisc_1(A_2637, B_2638, C_2639)) | k1_xboole_0=C_2639 | k1_xboole_0=B_2638 | k1_xboole_0=A_2637)), inference(cnfTransformation, [status(thm)], [f_607])).
% 16.85/7.54  tff(c_42361, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38', k7_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'))='#skF_38' | ~m1_subset_1('#skF_38', k3_zfmisc_1('#skF_35', '#skF_36', '#skF_37')) | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(superposition, [status(thm), theory('equality')], [c_28424, c_42313])).
% 16.85/7.54  tff(c_42368, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38', k2_mcart_1('#skF_38'))='#skF_38' | k1_xboole_0='#skF_37' | k1_xboole_0='#skF_36' | k1_xboole_0='#skF_35'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_39453, c_42361])).
% 16.85/7.54  tff(c_42369, plain, (k3_mcart_1(k5_mcart_1('#skF_35', '#skF_36', '#skF_37', '#skF_38'), '#skF_38', k2_mcart_1('#skF_38'))='#skF_38'), inference(negUnitSimplification, [status(thm)], [c_368, c_366, c_364, c_42368])).
% 16.85/7.54  tff(c_28499, plain, (![A_1936, B_1937]: (k2_xboole_0(k1_tarski(A_1936), B_1937)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_180])).
% 16.85/7.54  tff(c_28503, plain, (![A_1936]: (k1_tarski(A_1936)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_24, c_28499])).
% 16.85/7.54  tff(c_34248, plain, (![A_2331, B_2332, C_2333]: (k3_zfmisc_1(k1_tarski(A_2331), k1_tarski(B_2332), k1_tarski(C_2333))=k1_tarski(k3_mcart_1(A_2331, B_2332, C_2333)))), inference(cnfTransformation, [status(thm)], [f_585])).
% 16.85/7.54  tff(c_348, plain, (![A_409, C_411, B_410]: (~r1_tarski(A_409, k3_zfmisc_1(C_411, A_409, B_410)) | k1_xboole_0=A_409)), inference(cnfTransformation, [status(thm)], [f_619])).
% 16.85/7.54  tff(c_34284, plain, (![B_2332, A_2331, C_2333]: (~r1_tarski(k1_tarski(B_2332), k1_tarski(k3_mcart_1(A_2331, B_2332, C_2333))) | k1_tarski(B_2332)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_34248, c_348])).
% 16.85/7.54  tff(c_34297, plain, (![B_2332, A_2331, C_2333]: (~r1_tarski(k1_tarski(B_2332), k1_tarski(k3_mcart_1(A_2331, B_2332, C_2333))))), inference(negUnitSimplification, [status(thm)], [c_28503, c_34284])).
% 16.85/7.54  tff(c_42398, plain, (~r1_tarski(k1_tarski('#skF_38'), k1_tarski('#skF_38'))), inference(superposition, [status(thm), theory('equality')], [c_42369, c_34297])).
% 16.85/7.54  tff(c_42424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_42398])).
% 16.85/7.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/7.54  
% 16.85/7.54  Inference rules
% 16.85/7.54  ----------------------
% 16.85/7.54  #Ref     : 14
% 16.85/7.54  #Sup     : 9698
% 16.85/7.54  #Fact    : 24
% 16.85/7.54  #Define  : 0
% 16.85/7.54  #Split   : 35
% 16.85/7.54  #Chain   : 0
% 16.85/7.54  #Close   : 0
% 16.85/7.54  
% 16.85/7.54  Ordering : KBO
% 16.85/7.54  
% 16.85/7.54  Simplification rules
% 16.85/7.54  ----------------------
% 16.85/7.54  #Subsume      : 2857
% 16.85/7.54  #Demod        : 2578
% 16.85/7.54  #Tautology    : 2703
% 16.85/7.54  #SimpNegUnit  : 699
% 16.85/7.54  #BackRed      : 30
% 16.85/7.54  
% 16.85/7.54  #Partial instantiations: 0
% 16.85/7.54  #Strategies tried      : 1
% 16.85/7.54  
% 16.85/7.54  Timing (in seconds)
% 16.85/7.54  ----------------------
% 16.85/7.55  Preprocessing        : 0.55
% 16.85/7.55  Parsing              : 0.26
% 16.85/7.55  CNF conversion       : 0.06
% 16.85/7.55  Main loop            : 6.20
% 16.85/7.55  Inferencing          : 1.43
% 16.85/7.55  Reduction            : 2.53
% 16.85/7.55  Demodulation         : 1.78
% 16.85/7.55  BG Simplification    : 0.15
% 16.85/7.55  Subsumption          : 1.64
% 16.85/7.55  Abstraction          : 0.16
% 16.85/7.55  MUC search           : 0.00
% 16.85/7.55  Cooper               : 0.00
% 16.85/7.55  Total                : 6.80
% 16.85/7.55  Index Insertion      : 0.00
% 16.85/7.55  Index Deletion       : 0.00
% 16.85/7.55  Index Matching       : 0.00
% 16.85/7.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
