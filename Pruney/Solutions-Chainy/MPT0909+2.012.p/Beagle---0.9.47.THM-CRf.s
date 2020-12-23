%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:58 EST 2020

% Result     : Theorem 9.42s
% Output     : CNFRefutation 9.42s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 273 expanded)
%              Number of leaves         :   31 ( 111 expanded)
%              Depth                    :   11
%              Number of atoms          :  195 ( 944 expanded)
%              Number of equality atoms :   85 ( 512 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_125,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_34,plain,(
    k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_229,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_mcart_1(A_96,B_97,C_98,D_99) = k2_mcart_1(D_99)
      | ~ m1_subset_1(D_99,k3_zfmisc_1(A_96,B_97,C_98))
      | k1_xboole_0 = C_98
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_248,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_229])).

tff(c_264,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_248])).

tff(c_12,plain,(
    ! [A_12,B_13,C_14,D_15] :
      ( m1_subset_1(k7_mcart_1(A_12,B_13,C_14,D_15),C_14)
      | ~ m1_subset_1(D_15,k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_271,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_12])).

tff(c_275,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_271])).

tff(c_524,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k3_mcart_1(k5_mcart_1(A_122,B_123,C_124,D_125),k6_mcart_1(A_122,B_123,C_124,D_125),k7_mcart_1(A_122,B_123,C_124,D_125)) = D_125
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_535,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_524])).

tff(c_539,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_535])).

tff(c_540,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_539])).

tff(c_42,plain,(
    ! [F_39,G_43,H_45] :
      ( F_39 = '#skF_4'
      | k3_mcart_1(F_39,G_43,H_45) != '#skF_5'
      | ~ m1_subset_1(H_45,'#skF_3')
      | ~ m1_subset_1(G_43,'#skF_2')
      | ~ m1_subset_1(F_39,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_602,plain,
    ( k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_540,c_42])).

tff(c_607,plain,
    ( k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_275,c_602])).

tff(c_608,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_607])).

tff(c_745,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_608])).

tff(c_311,plain,(
    ! [A_104,B_105,C_106,D_107] :
      ( k5_mcart_1(A_104,B_105,C_106,D_107) = k1_mcart_1(k1_mcart_1(D_107))
      | ~ m1_subset_1(D_107,k3_zfmisc_1(A_104,B_105,C_106))
      | k1_xboole_0 = C_106
      | k1_xboole_0 = B_105
      | k1_xboole_0 = A_104 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_330,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_311])).

tff(c_346,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_330])).

tff(c_10,plain,(
    ! [A_9,B_10,C_11] : k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11) = k3_zfmisc_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r2_hidden(A_4,B_5)
      | v1_xboole_0(B_5)
      | ~ m1_subset_1(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    ! [A_66,C_67,B_68] :
      ( r2_hidden(k2_mcart_1(A_66),C_67)
      | ~ r2_hidden(A_66,k2_zfmisc_1(B_68,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4200,plain,(
    ! [A_380,C_381,B_382] :
      ( r2_hidden(k2_mcart_1(A_380),C_381)
      | v1_xboole_0(k2_zfmisc_1(B_382,C_381))
      | ~ m1_subset_1(A_380,k2_zfmisc_1(B_382,C_381)) ) ),
    inference(resolution,[status(thm)],[c_6,c_118])).

tff(c_4273,plain,(
    ! [A_380,C_11,A_9,B_10] :
      ( r2_hidden(k2_mcart_1(A_380),C_11)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11))
      | ~ m1_subset_1(A_380,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_4200])).

tff(c_5538,plain,(
    ! [A_458,C_459,A_460,B_461] :
      ( r2_hidden(k2_mcart_1(A_458),C_459)
      | v1_xboole_0(k3_zfmisc_1(A_460,B_461,C_459))
      | ~ m1_subset_1(A_458,k3_zfmisc_1(A_460,B_461,C_459)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4273])).

tff(c_5673,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_5538])).

tff(c_5677,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5673])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5681,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5677,c_2])).

tff(c_18,plain,(
    ! [A_19,B_20,C_21] :
      ( k3_zfmisc_1(A_19,B_20,C_21) != k1_xboole_0
      | k1_xboole_0 = C_21
      | k1_xboole_0 = B_20
      | k1_xboole_0 = A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_5720,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_5681,c_18])).

tff(c_5742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_5720])).

tff(c_5744,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5673])).

tff(c_113,plain,(
    ! [A_63,B_64,C_65] :
      ( r2_hidden(k1_mcart_1(A_63),B_64)
      | ~ r2_hidden(A_63,k2_zfmisc_1(B_64,C_65)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3953,plain,(
    ! [A_365,B_366,C_367] :
      ( r2_hidden(k1_mcart_1(A_365),B_366)
      | v1_xboole_0(k2_zfmisc_1(B_366,C_367))
      | ~ m1_subset_1(A_365,k2_zfmisc_1(B_366,C_367)) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_4017,plain,(
    ! [A_365,A_9,B_10,C_11] :
      ( r2_hidden(k1_mcart_1(A_365),k2_zfmisc_1(A_9,B_10))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11))
      | ~ m1_subset_1(A_365,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_3953])).

tff(c_6298,plain,(
    ! [A_497,A_498,B_499,C_500] :
      ( r2_hidden(k1_mcart_1(A_497),k2_zfmisc_1(A_498,B_499))
      | v1_xboole_0(k3_zfmisc_1(A_498,B_499,C_500))
      | ~ m1_subset_1(A_497,k3_zfmisc_1(A_498,B_499,C_500)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_4017])).

tff(c_6395,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_6298])).

tff(c_6436,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_5744,c_6395])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k1_mcart_1(A_16),B_17)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6443,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6436,c_16])).

tff(c_6450,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_346,c_6443])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,B_3)
      | ~ r2_hidden(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6466,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_6450,c_4])).

tff(c_6470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_745,c_6466])).

tff(c_6471,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_608])).

tff(c_371,plain,(
    ! [A_110,B_111,C_112,D_113] :
      ( k6_mcart_1(A_110,B_111,C_112,D_113) = k2_mcart_1(k1_mcart_1(D_113))
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_110,B_111,C_112))
      | k1_xboole_0 = C_112
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_110 ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_390,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_371])).

tff(c_406,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_390])).

tff(c_123,plain,(
    ! [A_69,B_70,C_71] : k2_zfmisc_1(k2_zfmisc_1(A_69,B_70),C_71) = k3_zfmisc_1(A_69,B_70,C_71) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(k2_mcart_1(A_16),C_18)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_142,plain,(
    ! [A_72,C_73,A_74,B_75] :
      ( r2_hidden(k2_mcart_1(A_72),C_73)
      | ~ r2_hidden(A_72,k3_zfmisc_1(A_74,B_75,C_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_14])).

tff(c_10926,plain,(
    ! [A_777,C_778,A_779,B_780] :
      ( r2_hidden(k2_mcart_1(A_777),C_778)
      | v1_xboole_0(k3_zfmisc_1(A_779,B_780,C_778))
      | ~ m1_subset_1(A_777,k3_zfmisc_1(A_779,B_780,C_778)) ) ),
    inference(resolution,[status(thm)],[c_6,c_142])).

tff(c_11061,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_10926])).

tff(c_11065,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11061])).

tff(c_11069,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_11065,c_2])).

tff(c_11108,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_11069,c_18])).

tff(c_11130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_38,c_36,c_11108])).

tff(c_11132,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_11061])).

tff(c_9613,plain,(
    ! [A_705,B_706,C_707] :
      ( r2_hidden(k1_mcart_1(A_705),B_706)
      | v1_xboole_0(k2_zfmisc_1(B_706,C_707))
      | ~ m1_subset_1(A_705,k2_zfmisc_1(B_706,C_707)) ) ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_9674,plain,(
    ! [A_705,A_9,B_10,C_11] :
      ( r2_hidden(k1_mcart_1(A_705),k2_zfmisc_1(A_9,B_10))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9,B_10),C_11))
      | ~ m1_subset_1(A_705,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_9613])).

tff(c_11577,plain,(
    ! [A_810,A_811,B_812,C_813] :
      ( r2_hidden(k1_mcart_1(A_810),k2_zfmisc_1(A_811,B_812))
      | v1_xboole_0(k3_zfmisc_1(A_811,B_812,C_813))
      | ~ m1_subset_1(A_810,k3_zfmisc_1(A_811,B_812,C_813)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_9674])).

tff(c_11674,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_44,c_11577])).

tff(c_11715,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_11132,c_11674])).

tff(c_11720,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_11715,c_14])).

tff(c_11727,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_11720])).

tff(c_11741,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_11727,c_4])).

tff(c_11745,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6471,c_11741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:01:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.42/3.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.42  
% 9.42/3.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.43  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.42/3.43  
% 9.42/3.43  %Foreground sorts:
% 9.42/3.43  
% 9.42/3.43  
% 9.42/3.43  %Background operators:
% 9.42/3.43  
% 9.42/3.43  
% 9.42/3.43  %Foreground operators:
% 9.42/3.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.42/3.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.42/3.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 9.42/3.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.42/3.43  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 9.42/3.43  tff('#skF_5', type, '#skF_5': $i).
% 9.42/3.43  tff('#skF_2', type, '#skF_2': $i).
% 9.42/3.43  tff('#skF_3', type, '#skF_3': $i).
% 9.42/3.43  tff('#skF_1', type, '#skF_1': $i).
% 9.42/3.43  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 9.42/3.43  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.42/3.43  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 9.42/3.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.42/3.43  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.42/3.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.42/3.43  tff('#skF_4', type, '#skF_4': $i).
% 9.42/3.43  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 9.42/3.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.42/3.43  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.42/3.43  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.42/3.43  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.42/3.43  
% 9.42/3.44  tff(f_125, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 9.42/3.44  tff(f_101, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 9.42/3.44  tff(f_47, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 9.42/3.44  tff(f_81, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 9.42/3.44  tff(f_43, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.42/3.44  tff(f_39, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 9.42/3.44  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 9.42/3.44  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 9.42/3.44  tff(f_65, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 9.42/3.44  tff(f_33, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 9.42/3.44  tff(c_34, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_44, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_36, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_229, plain, (![A_96, B_97, C_98, D_99]: (k7_mcart_1(A_96, B_97, C_98, D_99)=k2_mcart_1(D_99) | ~m1_subset_1(D_99, k3_zfmisc_1(A_96, B_97, C_98)) | k1_xboole_0=C_98 | k1_xboole_0=B_97 | k1_xboole_0=A_96)), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.42/3.44  tff(c_248, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_229])).
% 9.42/3.44  tff(c_264, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_248])).
% 9.42/3.44  tff(c_12, plain, (![A_12, B_13, C_14, D_15]: (m1_subset_1(k7_mcart_1(A_12, B_13, C_14, D_15), C_14) | ~m1_subset_1(D_15, k3_zfmisc_1(A_12, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 9.42/3.44  tff(c_271, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_264, c_12])).
% 9.42/3.44  tff(c_275, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_271])).
% 9.42/3.44  tff(c_524, plain, (![A_122, B_123, C_124, D_125]: (k3_mcart_1(k5_mcart_1(A_122, B_123, C_124, D_125), k6_mcart_1(A_122, B_123, C_124, D_125), k7_mcart_1(A_122, B_123, C_124, D_125))=D_125 | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.42/3.44  tff(c_535, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_264, c_524])).
% 9.42/3.44  tff(c_539, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_535])).
% 9.42/3.44  tff(c_540, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_539])).
% 9.42/3.44  tff(c_42, plain, (![F_39, G_43, H_45]: (F_39='#skF_4' | k3_mcart_1(F_39, G_43, H_45)!='#skF_5' | ~m1_subset_1(H_45, '#skF_3') | ~m1_subset_1(G_43, '#skF_2') | ~m1_subset_1(F_39, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.42/3.44  tff(c_602, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_540, c_42])).
% 9.42/3.44  tff(c_607, plain, (k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_275, c_602])).
% 9.42/3.45  tff(c_608, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_607])).
% 9.42/3.45  tff(c_745, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_608])).
% 9.42/3.45  tff(c_311, plain, (![A_104, B_105, C_106, D_107]: (k5_mcart_1(A_104, B_105, C_106, D_107)=k1_mcart_1(k1_mcart_1(D_107)) | ~m1_subset_1(D_107, k3_zfmisc_1(A_104, B_105, C_106)) | k1_xboole_0=C_106 | k1_xboole_0=B_105 | k1_xboole_0=A_104)), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.42/3.45  tff(c_330, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_311])).
% 9.42/3.45  tff(c_346, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_330])).
% 9.42/3.45  tff(c_10, plain, (![A_9, B_10, C_11]: (k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)=k3_zfmisc_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.42/3.45  tff(c_6, plain, (![A_4, B_5]: (r2_hidden(A_4, B_5) | v1_xboole_0(B_5) | ~m1_subset_1(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.42/3.45  tff(c_118, plain, (![A_66, C_67, B_68]: (r2_hidden(k2_mcart_1(A_66), C_67) | ~r2_hidden(A_66, k2_zfmisc_1(B_68, C_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.42/3.45  tff(c_4200, plain, (![A_380, C_381, B_382]: (r2_hidden(k2_mcart_1(A_380), C_381) | v1_xboole_0(k2_zfmisc_1(B_382, C_381)) | ~m1_subset_1(A_380, k2_zfmisc_1(B_382, C_381)))), inference(resolution, [status(thm)], [c_6, c_118])).
% 9.42/3.45  tff(c_4273, plain, (![A_380, C_11, A_9, B_10]: (r2_hidden(k2_mcart_1(A_380), C_11) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)) | ~m1_subset_1(A_380, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_4200])).
% 9.42/3.45  tff(c_5538, plain, (![A_458, C_459, A_460, B_461]: (r2_hidden(k2_mcart_1(A_458), C_459) | v1_xboole_0(k3_zfmisc_1(A_460, B_461, C_459)) | ~m1_subset_1(A_458, k3_zfmisc_1(A_460, B_461, C_459)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4273])).
% 9.42/3.45  tff(c_5673, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_5538])).
% 9.42/3.45  tff(c_5677, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_5673])).
% 9.42/3.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 9.42/3.45  tff(c_5681, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_5677, c_2])).
% 9.42/3.45  tff(c_18, plain, (![A_19, B_20, C_21]: (k3_zfmisc_1(A_19, B_20, C_21)!=k1_xboole_0 | k1_xboole_0=C_21 | k1_xboole_0=B_20 | k1_xboole_0=A_19)), inference(cnfTransformation, [status(thm)], [f_65])).
% 9.42/3.45  tff(c_5720, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_5681, c_18])).
% 9.42/3.45  tff(c_5742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_5720])).
% 9.42/3.45  tff(c_5744, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_5673])).
% 9.42/3.45  tff(c_113, plain, (![A_63, B_64, C_65]: (r2_hidden(k1_mcart_1(A_63), B_64) | ~r2_hidden(A_63, k2_zfmisc_1(B_64, C_65)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.42/3.45  tff(c_3953, plain, (![A_365, B_366, C_367]: (r2_hidden(k1_mcart_1(A_365), B_366) | v1_xboole_0(k2_zfmisc_1(B_366, C_367)) | ~m1_subset_1(A_365, k2_zfmisc_1(B_366, C_367)))), inference(resolution, [status(thm)], [c_6, c_113])).
% 9.42/3.45  tff(c_4017, plain, (![A_365, A_9, B_10, C_11]: (r2_hidden(k1_mcart_1(A_365), k2_zfmisc_1(A_9, B_10)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)) | ~m1_subset_1(A_365, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_3953])).
% 9.42/3.45  tff(c_6298, plain, (![A_497, A_498, B_499, C_500]: (r2_hidden(k1_mcart_1(A_497), k2_zfmisc_1(A_498, B_499)) | v1_xboole_0(k3_zfmisc_1(A_498, B_499, C_500)) | ~m1_subset_1(A_497, k3_zfmisc_1(A_498, B_499, C_500)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_4017])).
% 9.42/3.45  tff(c_6395, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_6298])).
% 9.42/3.45  tff(c_6436, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_5744, c_6395])).
% 9.42/3.45  tff(c_16, plain, (![A_16, B_17, C_18]: (r2_hidden(k1_mcart_1(A_16), B_17) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.42/3.45  tff(c_6443, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_6436, c_16])).
% 9.42/3.45  tff(c_6450, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_346, c_6443])).
% 9.42/3.45  tff(c_4, plain, (![A_2, B_3]: (m1_subset_1(A_2, B_3) | ~r2_hidden(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.42/3.45  tff(c_6466, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_6450, c_4])).
% 9.42/3.45  tff(c_6470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_745, c_6466])).
% 9.42/3.45  tff(c_6471, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_608])).
% 9.42/3.45  tff(c_371, plain, (![A_110, B_111, C_112, D_113]: (k6_mcart_1(A_110, B_111, C_112, D_113)=k2_mcart_1(k1_mcart_1(D_113)) | ~m1_subset_1(D_113, k3_zfmisc_1(A_110, B_111, C_112)) | k1_xboole_0=C_112 | k1_xboole_0=B_111 | k1_xboole_0=A_110)), inference(cnfTransformation, [status(thm)], [f_101])).
% 9.42/3.45  tff(c_390, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_44, c_371])).
% 9.42/3.45  tff(c_406, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_390])).
% 9.42/3.45  tff(c_123, plain, (![A_69, B_70, C_71]: (k2_zfmisc_1(k2_zfmisc_1(A_69, B_70), C_71)=k3_zfmisc_1(A_69, B_70, C_71))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.42/3.45  tff(c_14, plain, (![A_16, C_18, B_17]: (r2_hidden(k2_mcart_1(A_16), C_18) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.42/3.45  tff(c_142, plain, (![A_72, C_73, A_74, B_75]: (r2_hidden(k2_mcart_1(A_72), C_73) | ~r2_hidden(A_72, k3_zfmisc_1(A_74, B_75, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_14])).
% 9.42/3.45  tff(c_10926, plain, (![A_777, C_778, A_779, B_780]: (r2_hidden(k2_mcart_1(A_777), C_778) | v1_xboole_0(k3_zfmisc_1(A_779, B_780, C_778)) | ~m1_subset_1(A_777, k3_zfmisc_1(A_779, B_780, C_778)))), inference(resolution, [status(thm)], [c_6, c_142])).
% 9.42/3.45  tff(c_11061, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_10926])).
% 9.42/3.45  tff(c_11065, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_11061])).
% 9.42/3.45  tff(c_11069, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_11065, c_2])).
% 9.42/3.45  tff(c_11108, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_11069, c_18])).
% 9.42/3.45  tff(c_11130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_38, c_36, c_11108])).
% 9.42/3.45  tff(c_11132, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_11061])).
% 9.42/3.45  tff(c_9613, plain, (![A_705, B_706, C_707]: (r2_hidden(k1_mcart_1(A_705), B_706) | v1_xboole_0(k2_zfmisc_1(B_706, C_707)) | ~m1_subset_1(A_705, k2_zfmisc_1(B_706, C_707)))), inference(resolution, [status(thm)], [c_6, c_113])).
% 9.42/3.45  tff(c_9674, plain, (![A_705, A_9, B_10, C_11]: (r2_hidden(k1_mcart_1(A_705), k2_zfmisc_1(A_9, B_10)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_9, B_10), C_11)) | ~m1_subset_1(A_705, k3_zfmisc_1(A_9, B_10, C_11)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_9613])).
% 9.42/3.45  tff(c_11577, plain, (![A_810, A_811, B_812, C_813]: (r2_hidden(k1_mcart_1(A_810), k2_zfmisc_1(A_811, B_812)) | v1_xboole_0(k3_zfmisc_1(A_811, B_812, C_813)) | ~m1_subset_1(A_810, k3_zfmisc_1(A_811, B_812, C_813)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_9674])).
% 9.42/3.45  tff(c_11674, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_44, c_11577])).
% 9.42/3.45  tff(c_11715, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_11132, c_11674])).
% 9.42/3.45  tff(c_11720, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_11715, c_14])).
% 9.42/3.45  tff(c_11727, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_406, c_11720])).
% 9.42/3.45  tff(c_11741, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_11727, c_4])).
% 9.42/3.45  tff(c_11745, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6471, c_11741])).
% 9.42/3.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.42/3.45  
% 9.42/3.45  Inference rules
% 9.42/3.45  ----------------------
% 9.42/3.45  #Ref     : 0
% 9.42/3.45  #Sup     : 3035
% 9.42/3.45  #Fact    : 0
% 9.42/3.45  #Define  : 0
% 9.42/3.45  #Split   : 18
% 9.42/3.45  #Chain   : 0
% 9.42/3.45  #Close   : 0
% 9.42/3.45  
% 9.42/3.45  Ordering : KBO
% 9.42/3.45  
% 9.42/3.45  Simplification rules
% 9.42/3.45  ----------------------
% 9.42/3.45  #Subsume      : 794
% 9.42/3.45  #Demod        : 675
% 9.42/3.45  #Tautology    : 344
% 9.42/3.45  #SimpNegUnit  : 43
% 9.42/3.45  #BackRed      : 8
% 9.42/3.45  
% 9.42/3.45  #Partial instantiations: 0
% 9.42/3.45  #Strategies tried      : 1
% 9.42/3.45  
% 9.42/3.45  Timing (in seconds)
% 9.42/3.45  ----------------------
% 9.42/3.45  Preprocessing        : 0.35
% 9.42/3.45  Parsing              : 0.19
% 9.42/3.45  CNF conversion       : 0.02
% 9.42/3.45  Main loop            : 2.33
% 9.42/3.45  Inferencing          : 0.68
% 9.42/3.45  Reduction            : 0.57
% 9.42/3.45  Demodulation         : 0.37
% 9.42/3.45  BG Simplification    : 0.09
% 9.42/3.45  Subsumption          : 0.81
% 9.42/3.45  Abstraction          : 0.13
% 9.42/3.45  MUC search           : 0.00
% 9.42/3.45  Cooper               : 0.00
% 9.42/3.45  Total                : 2.72
% 9.42/3.45  Index Insertion      : 0.00
% 9.42/3.45  Index Deletion       : 0.00
% 9.42/3.45  Index Matching       : 0.00
% 9.42/3.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
