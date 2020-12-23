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
% DateTime   : Thu Dec  3 10:10:05 EST 2020

% Result     : Theorem 2.87s
% Output     : CNFRefutation 3.02s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 322 expanded)
%              Number of leaves         :   34 ( 124 expanded)
%              Depth                    :   15
%              Number of atoms          :  171 ( 935 expanded)
%              Number of equality atoms :   73 ( 440 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_114,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_90,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & ~ v1_xboole_0(B) )
     => ~ v1_xboole_0(k2_zfmisc_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_subset_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_52,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_40,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_159,plain,(
    ! [A_96,B_97,C_98,D_99] :
      ( k7_mcart_1(A_96,B_97,C_98,D_99) = k2_mcart_1(D_99)
      | ~ m1_subset_1(D_99,k3_zfmisc_1(A_96,B_97,C_98))
      | k1_xboole_0 = C_98
      | k1_xboole_0 = B_97
      | k1_xboole_0 = A_96 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_169,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_159])).

tff(c_173,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_169])).

tff(c_30,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_174,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_30])).

tff(c_16,plain,(
    ! [A_16,B_17,C_18,D_19] :
      ( m1_subset_1(k7_mcart_1(A_16,B_17,C_18,D_19),C_18)
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_16,B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_178,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_16])).

tff(c_182,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_178])).

tff(c_66,plain,(
    ! [A_59,B_60,C_61] : k2_zfmisc_1(k2_zfmisc_1(A_59,B_60),C_61) = k3_zfmisc_1(A_59,B_60,C_61) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_59,B_60,C_61] : v1_relat_1(k3_zfmisc_1(A_59,B_60,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_10])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_106,plain,(
    ! [A_75,B_76] :
      ( k4_tarski(k1_mcart_1(A_75),k2_mcart_1(A_75)) = A_75
      | ~ r2_hidden(A_75,B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_196,plain,(
    ! [A_107,B_108] :
      ( k4_tarski(k1_mcart_1(A_107),k2_mcart_1(A_107)) = A_107
      | ~ v1_relat_1(B_108)
      | v1_xboole_0(B_108)
      | ~ m1_subset_1(A_107,B_108) ) ),
    inference(resolution,[status(thm)],[c_8,c_106])).

tff(c_202,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_196])).

tff(c_207,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_202])).

tff(c_208,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_207])).

tff(c_4,plain,(
    ! [A_2,B_3] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_2,B_3))
      | v1_xboole_0(B_3)
      | v1_xboole_0(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_75,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_59,B_60,C_61))
      | v1_xboole_0(C_61)
      | v1_xboole_0(k2_zfmisc_1(A_59,B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_4])).

tff(c_215,plain,
    ( v1_xboole_0('#skF_3')
    | v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_208,c_75])).

tff(c_270,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_277,plain,
    ( v1_xboole_0('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_270,c_4])).

tff(c_279,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_277])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_282,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_279,c_2])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_282])).

tff(c_287,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_277])).

tff(c_304,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_304])).

tff(c_309,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_313,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_309,c_2])).

tff(c_317,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_313])).

tff(c_318,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_354,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k5_mcart_1(A_122,B_123,C_124,D_125) = k1_mcart_1(k1_mcart_1(D_125))
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_364,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_354])).

tff(c_368,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_364])).

tff(c_319,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_207])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),C_15) = k3_zfmisc_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_87,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden(k1_mcart_1(A_65),B_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_66,C_67)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_112,plain,(
    ! [A_84,A_85,B_86,C_87] :
      ( r2_hidden(k1_mcart_1(A_84),k2_zfmisc_1(A_85,B_86))
      | ~ r2_hidden(A_84,k3_zfmisc_1(A_85,B_86,C_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_87])).

tff(c_395,plain,(
    ! [A_130,A_131,B_132,C_133] :
      ( r2_hidden(k1_mcart_1(A_130),k2_zfmisc_1(A_131,B_132))
      | v1_xboole_0(k3_zfmisc_1(A_131,B_132,C_133))
      | ~ m1_subset_1(A_130,k3_zfmisc_1(A_131,B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_8,c_112])).

tff(c_402,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_40,c_395])).

tff(c_407,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_319,c_402])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( r2_hidden(k1_mcart_1(A_20),B_21)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_407,c_20])).

tff(c_422,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_368,c_413])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,B_5)
      | ~ r2_hidden(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_468,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_422,c_6])).

tff(c_431,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k6_mcart_1(A_134,B_135,C_136,D_137) = k2_mcart_1(k1_mcart_1(D_137))
      | ~ m1_subset_1(D_137,k3_zfmisc_1(A_134,B_135,C_136))
      | k1_xboole_0 = C_136
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_441,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_40,c_431])).

tff(c_445,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_441])).

tff(c_18,plain,(
    ! [A_20,C_22,B_21] :
      ( r2_hidden(k2_mcart_1(A_20),C_22)
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_21,C_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_420,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_407,c_18])).

tff(c_430,plain,(
    m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_420,c_6])).

tff(c_469,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_430])).

tff(c_22,plain,(
    ! [A_23,B_24] :
      ( k4_tarski(k1_mcart_1(A_23),k2_mcart_1(A_23)) = A_23
      | ~ r2_hidden(A_23,B_24)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_409,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_407,c_22])).

tff(c_419,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_368,c_409])).

tff(c_489,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_419])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k4_tarski(k4_tarski(A_10,B_11),C_12) = k3_mcart_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_515,plain,(
    ! [C_144] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_144) = k4_tarski(k1_mcart_1('#skF_5'),C_144) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_12])).

tff(c_38,plain,(
    ! [H_43,F_37,G_41] :
      ( H_43 = '#skF_4'
      | k3_mcart_1(F_37,G_41,H_43) != '#skF_5'
      | ~ m1_subset_1(H_43,'#skF_3')
      | ~ m1_subset_1(G_41,'#skF_2')
      | ~ m1_subset_1(F_37,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_522,plain,(
    ! [C_144] :
      ( C_144 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_144) != '#skF_5'
      | ~ m1_subset_1(C_144,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_38])).

tff(c_531,plain,(
    ! [C_145] :
      ( C_145 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_145) != '#skF_5'
      | ~ m1_subset_1(C_145,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_469,c_522])).

tff(c_534,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_531])).

tff(c_537,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_182,c_534])).

tff(c_539,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_537])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:58:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.87/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.41  
% 2.87/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.87/1.42  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.87/1.42  
% 2.87/1.42  %Foreground sorts:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Background operators:
% 2.87/1.42  
% 2.87/1.42  
% 2.87/1.42  %Foreground operators:
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.87/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.87/1.42  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.87/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.87/1.42  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.87/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.87/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.87/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.87/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.87/1.42  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.87/1.42  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.87/1.42  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.87/1.42  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.87/1.42  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.87/1.42  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.87/1.42  tff('#skF_4', type, '#skF_4': $i).
% 2.87/1.42  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.87/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.87/1.42  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.87/1.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.87/1.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.87/1.42  
% 3.02/1.43  tff(f_114, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.02/1.43  tff(f_90, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.02/1.43  tff(f_58, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 3.02/1.43  tff(f_54, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.02/1.43  tff(f_50, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.02/1.43  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.02/1.43  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.02/1.43  tff(f_38, axiom, (![A, B]: ((~v1_xboole_0(A) & ~v1_xboole_0(B)) => ~v1_xboole_0(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_subset_1)).
% 3.02/1.43  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.02/1.43  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.02/1.43  tff(f_42, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 3.02/1.43  tff(f_52, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.02/1.43  tff(c_36, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.43  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.43  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.43  tff(c_40, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.43  tff(c_159, plain, (![A_96, B_97, C_98, D_99]: (k7_mcart_1(A_96, B_97, C_98, D_99)=k2_mcart_1(D_99) | ~m1_subset_1(D_99, k3_zfmisc_1(A_96, B_97, C_98)) | k1_xboole_0=C_98 | k1_xboole_0=B_97 | k1_xboole_0=A_96)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.02/1.43  tff(c_169, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_40, c_159])).
% 3.02/1.43  tff(c_173, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_169])).
% 3.02/1.43  tff(c_30, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.43  tff(c_174, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_30])).
% 3.02/1.43  tff(c_16, plain, (![A_16, B_17, C_18, D_19]: (m1_subset_1(k7_mcart_1(A_16, B_17, C_18, D_19), C_18) | ~m1_subset_1(D_19, k3_zfmisc_1(A_16, B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.02/1.43  tff(c_178, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_173, c_16])).
% 3.02/1.43  tff(c_182, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_178])).
% 3.02/1.43  tff(c_66, plain, (![A_59, B_60, C_61]: (k2_zfmisc_1(k2_zfmisc_1(A_59, B_60), C_61)=k3_zfmisc_1(A_59, B_60, C_61))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.02/1.43  tff(c_10, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.02/1.43  tff(c_77, plain, (![A_59, B_60, C_61]: (v1_relat_1(k3_zfmisc_1(A_59, B_60, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_10])).
% 3.02/1.43  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.02/1.43  tff(c_106, plain, (![A_75, B_76]: (k4_tarski(k1_mcart_1(A_75), k2_mcart_1(A_75))=A_75 | ~r2_hidden(A_75, B_76) | ~v1_relat_1(B_76))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.43  tff(c_196, plain, (![A_107, B_108]: (k4_tarski(k1_mcart_1(A_107), k2_mcart_1(A_107))=A_107 | ~v1_relat_1(B_108) | v1_xboole_0(B_108) | ~m1_subset_1(A_107, B_108))), inference(resolution, [status(thm)], [c_8, c_106])).
% 3.02/1.43  tff(c_202, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_196])).
% 3.02/1.43  tff(c_207, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_77, c_202])).
% 3.02/1.43  tff(c_208, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_207])).
% 3.02/1.43  tff(c_4, plain, (![A_2, B_3]: (~v1_xboole_0(k2_zfmisc_1(A_2, B_3)) | v1_xboole_0(B_3) | v1_xboole_0(A_2))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.02/1.43  tff(c_75, plain, (![A_59, B_60, C_61]: (~v1_xboole_0(k3_zfmisc_1(A_59, B_60, C_61)) | v1_xboole_0(C_61) | v1_xboole_0(k2_zfmisc_1(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_4])).
% 3.02/1.43  tff(c_215, plain, (v1_xboole_0('#skF_3') | v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_208, c_75])).
% 3.02/1.43  tff(c_270, plain, (v1_xboole_0(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_215])).
% 3.02/1.43  tff(c_277, plain, (v1_xboole_0('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_270, c_4])).
% 3.02/1.43  tff(c_279, plain, (v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_277])).
% 3.02/1.43  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.02/1.43  tff(c_282, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_279, c_2])).
% 3.02/1.43  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_282])).
% 3.02/1.43  tff(c_287, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_277])).
% 3.02/1.43  tff(c_304, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_287, c_2])).
% 3.02/1.43  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_304])).
% 3.02/1.43  tff(c_309, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_215])).
% 3.02/1.43  tff(c_313, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_309, c_2])).
% 3.02/1.43  tff(c_317, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_313])).
% 3.02/1.43  tff(c_318, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_207])).
% 3.02/1.43  tff(c_354, plain, (![A_122, B_123, C_124, D_125]: (k5_mcart_1(A_122, B_123, C_124, D_125)=k1_mcart_1(k1_mcart_1(D_125)) | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.02/1.43  tff(c_364, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_40, c_354])).
% 3.02/1.43  tff(c_368, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_364])).
% 3.02/1.43  tff(c_319, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_207])).
% 3.02/1.43  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.02/1.43  tff(c_87, plain, (![A_65, B_66, C_67]: (r2_hidden(k1_mcart_1(A_65), B_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.43  tff(c_112, plain, (![A_84, A_85, B_86, C_87]: (r2_hidden(k1_mcart_1(A_84), k2_zfmisc_1(A_85, B_86)) | ~r2_hidden(A_84, k3_zfmisc_1(A_85, B_86, C_87)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_87])).
% 3.02/1.43  tff(c_395, plain, (![A_130, A_131, B_132, C_133]: (r2_hidden(k1_mcart_1(A_130), k2_zfmisc_1(A_131, B_132)) | v1_xboole_0(k3_zfmisc_1(A_131, B_132, C_133)) | ~m1_subset_1(A_130, k3_zfmisc_1(A_131, B_132, C_133)))), inference(resolution, [status(thm)], [c_8, c_112])).
% 3.02/1.44  tff(c_402, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_40, c_395])).
% 3.02/1.44  tff(c_407, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_319, c_402])).
% 3.02/1.44  tff(c_20, plain, (![A_20, B_21, C_22]: (r2_hidden(k1_mcart_1(A_20), B_21) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.44  tff(c_413, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_407, c_20])).
% 3.02/1.44  tff(c_422, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_368, c_413])).
% 3.02/1.44  tff(c_6, plain, (![A_4, B_5]: (m1_subset_1(A_4, B_5) | ~r2_hidden(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.02/1.44  tff(c_468, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_422, c_6])).
% 3.02/1.44  tff(c_431, plain, (![A_134, B_135, C_136, D_137]: (k6_mcart_1(A_134, B_135, C_136, D_137)=k2_mcart_1(k1_mcart_1(D_137)) | ~m1_subset_1(D_137, k3_zfmisc_1(A_134, B_135, C_136)) | k1_xboole_0=C_136 | k1_xboole_0=B_135 | k1_xboole_0=A_134)), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.02/1.44  tff(c_441, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_40, c_431])).
% 3.02/1.44  tff(c_445, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_441])).
% 3.02/1.44  tff(c_18, plain, (![A_20, C_22, B_21]: (r2_hidden(k2_mcart_1(A_20), C_22) | ~r2_hidden(A_20, k2_zfmisc_1(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.02/1.44  tff(c_420, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_407, c_18])).
% 3.02/1.44  tff(c_430, plain, (m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_420, c_6])).
% 3.02/1.44  tff(c_469, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_430])).
% 3.02/1.44  tff(c_22, plain, (![A_23, B_24]: (k4_tarski(k1_mcart_1(A_23), k2_mcart_1(A_23))=A_23 | ~r2_hidden(A_23, B_24) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.02/1.44  tff(c_409, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_407, c_22])).
% 3.02/1.44  tff(c_419, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_368, c_409])).
% 3.02/1.44  tff(c_489, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_419])).
% 3.02/1.44  tff(c_12, plain, (![A_10, B_11, C_12]: (k4_tarski(k4_tarski(A_10, B_11), C_12)=k3_mcart_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.02/1.44  tff(c_515, plain, (![C_144]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_144)=k4_tarski(k1_mcart_1('#skF_5'), C_144))), inference(superposition, [status(thm), theory('equality')], [c_489, c_12])).
% 3.02/1.44  tff(c_38, plain, (![H_43, F_37, G_41]: (H_43='#skF_4' | k3_mcart_1(F_37, G_41, H_43)!='#skF_5' | ~m1_subset_1(H_43, '#skF_3') | ~m1_subset_1(G_41, '#skF_2') | ~m1_subset_1(F_37, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_114])).
% 3.02/1.44  tff(c_522, plain, (![C_144]: (C_144='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_144)!='#skF_5' | ~m1_subset_1(C_144, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_38])).
% 3.02/1.44  tff(c_531, plain, (![C_145]: (C_145='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_145)!='#skF_5' | ~m1_subset_1(C_145, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_468, c_469, c_522])).
% 3.02/1.44  tff(c_534, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_318, c_531])).
% 3.02/1.44  tff(c_537, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_182, c_534])).
% 3.02/1.44  tff(c_539, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_537])).
% 3.02/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.02/1.44  
% 3.02/1.44  Inference rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Ref     : 0
% 3.02/1.44  #Sup     : 121
% 3.02/1.44  #Fact    : 0
% 3.02/1.44  #Define  : 0
% 3.02/1.44  #Split   : 6
% 3.02/1.44  #Chain   : 0
% 3.02/1.44  #Close   : 0
% 3.02/1.44  
% 3.02/1.44  Ordering : KBO
% 3.02/1.44  
% 3.02/1.44  Simplification rules
% 3.02/1.44  ----------------------
% 3.02/1.44  #Subsume      : 10
% 3.02/1.44  #Demod        : 53
% 3.02/1.44  #Tautology    : 39
% 3.02/1.44  #SimpNegUnit  : 12
% 3.02/1.44  #BackRed      : 5
% 3.02/1.44  
% 3.02/1.44  #Partial instantiations: 0
% 3.02/1.44  #Strategies tried      : 1
% 3.02/1.44  
% 3.02/1.44  Timing (in seconds)
% 3.02/1.44  ----------------------
% 3.02/1.44  Preprocessing        : 0.31
% 3.02/1.44  Parsing              : 0.17
% 3.02/1.44  CNF conversion       : 0.02
% 3.02/1.44  Main loop            : 0.33
% 3.02/1.44  Inferencing          : 0.13
% 3.02/1.44  Reduction            : 0.10
% 3.02/1.44  Demodulation         : 0.07
% 3.02/1.44  BG Simplification    : 0.02
% 3.02/1.44  Subsumption          : 0.05
% 3.02/1.44  Abstraction          : 0.02
% 3.02/1.44  MUC search           : 0.00
% 3.02/1.44  Cooper               : 0.00
% 3.02/1.44  Total                : 0.68
% 3.02/1.44  Index Insertion      : 0.00
% 3.02/1.44  Index Deletion       : 0.00
% 3.02/1.44  Index Matching       : 0.00
% 3.02/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
