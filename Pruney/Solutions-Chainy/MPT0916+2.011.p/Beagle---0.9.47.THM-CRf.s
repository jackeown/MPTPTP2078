%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:11 EST 2020

% Result     : Theorem 4.51s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :  200 ( 567 expanded)
%              Number of leaves         :   32 ( 196 expanded)
%              Depth                    :    9
%              Number of atoms          :  328 (1574 expanded)
%              Number of equality atoms :  104 ( 476 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_99,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( r2_hidden(C,B)
         => r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_79,axiom,(
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

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_32,plain,(
    r2_hidden('#skF_9',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] : k2_zfmisc_1(k2_zfmisc_1(A_16,B_17),C_18) = k3_zfmisc_1(A_16,B_17,C_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1178,plain,(
    ! [A_230,C_231,B_232] :
      ( r2_hidden(k2_mcart_1(A_230),C_231)
      | ~ r2_hidden(A_230,k2_zfmisc_1(B_232,C_231)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1296,plain,(
    ! [A_249,C_250,A_251,B_252] :
      ( r2_hidden(k2_mcart_1(A_249),C_250)
      | ~ r2_hidden(A_249,k3_zfmisc_1(A_251,B_252,C_250)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1178])).

tff(c_1315,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_1296])).

tff(c_14,plain,(
    ! [C_13,A_10,B_11] :
      ( r2_hidden(C_13,A_10)
      | ~ r2_hidden(C_13,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1389,plain,(
    ! [A_261] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_261)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_261)) ) ),
    inference(resolution,[status(thm)],[c_1315,c_14])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1416,plain,(
    ! [A_262] :
      ( ~ v1_xboole_0(A_262)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_262)) ) ),
    inference(resolution,[status(thm)],[c_1389,c_2])).

tff(c_1420,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_1416])).

tff(c_122,plain,(
    ! [A_62,B_63,C_64] : k2_zfmisc_1(k2_zfmisc_1(A_62,B_63),C_64) = k3_zfmisc_1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_20,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    ! [A_75,C_76,A_77,B_78] :
      ( r2_hidden(k2_mcart_1(A_75),C_76)
      | ~ r2_hidden(A_75,k3_zfmisc_1(A_77,B_78,C_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_20])).

tff(c_221,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_206])).

tff(c_294,plain,(
    ! [A_86] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_86)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_221,c_14])).

tff(c_321,plain,(
    ! [A_87] :
      ( ~ v1_xboole_0(A_87)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_294,c_2])).

tff(c_325,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_321])).

tff(c_30,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8')
    | ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_51,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_38,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_170,plain,(
    ! [C_69,A_70,B_71] :
      ( r2_hidden(C_69,A_70)
      | ~ r2_hidden(C_69,B_71)
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_338,plain,(
    ! [A_90,A_91] :
      ( r2_hidden('#skF_1'(A_90),A_91)
      | ~ m1_subset_1(A_90,k1_zfmisc_1(A_91))
      | v1_xboole_0(A_90) ) ),
    inference(resolution,[status(thm)],[c_4,c_170])).

tff(c_365,plain,(
    ! [A_92,A_93] :
      ( ~ v1_xboole_0(A_92)
      | ~ m1_subset_1(A_93,k1_zfmisc_1(A_92))
      | v1_xboole_0(A_93) ) ),
    inference(resolution,[status(thm)],[c_338,c_2])).

tff(c_378,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_365])).

tff(c_385,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_378])).

tff(c_40,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_377,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_365])).

tff(c_379,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_377])).

tff(c_34,plain,(
    m1_subset_1('#skF_9',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_289,plain,(
    ! [A_82,B_83,C_84,D_85] :
      ( k7_mcart_1(A_82,B_83,C_84,D_85) = k2_mcart_1(D_85)
      | ~ m1_subset_1(D_85,k3_zfmisc_1(A_82,B_83,C_84))
      | k1_xboole_0 = C_84
      | k1_xboole_0 = B_83
      | k1_xboole_0 = A_82 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_293,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_289])).

tff(c_386,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_389,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_12])).

tff(c_391,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_389])).

tff(c_393,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_380,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k5_mcart_1(A_94,B_95,C_96,D_97) = k1_mcart_1(k1_mcart_1(D_97))
      | ~ m1_subset_1(D_97,k3_zfmisc_1(A_94,B_95,C_96))
      | k1_xboole_0 = C_96
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_384,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_380])).

tff(c_467,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_393,c_384])).

tff(c_468,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_467])).

tff(c_473,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_468,c_12])).

tff(c_475,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_385,c_473])).

tff(c_476,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_467])).

tff(c_491,plain,(
    k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_476])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_670,plain,(
    ! [A_145,A_146,B_147,C_148] :
      ( r2_hidden(k1_mcart_1(A_145),k2_zfmisc_1(A_146,B_147))
      | ~ r2_hidden(A_145,k3_zfmisc_1(A_146,B_147,C_148)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_22])).

tff(c_712,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_670])).

tff(c_718,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_712,c_22])).

tff(c_730,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_491,c_718])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_51,c_730])).

tff(c_733,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_476])).

tff(c_740,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_12])).

tff(c_742,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_325,c_740])).

tff(c_743,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_378])).

tff(c_94,plain,(
    ! [A_53,C_54,B_55] :
      ( r2_hidden(k2_mcart_1(A_53),C_54)
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_55,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_847,plain,(
    ! [B_169,C_170] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_169,C_170))),C_170)
      | v1_xboole_0(k2_zfmisc_1(B_169,C_170)) ) ),
    inference(resolution,[status(thm)],[c_4,c_94])).

tff(c_882,plain,(
    ! [C_171,B_172] :
      ( ~ v1_xboole_0(C_171)
      | v1_xboole_0(k2_zfmisc_1(B_172,C_171)) ) ),
    inference(resolution,[status(thm)],[c_847,c_2])).

tff(c_103,plain,(
    ! [A_56,B_57,C_58] :
      ( r2_hidden(k1_mcart_1(A_56),B_57)
      | ~ r2_hidden(A_56,k2_zfmisc_1(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_805,plain,(
    ! [B_162,C_163] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_162,C_163))),B_162)
      | v1_xboole_0(k2_zfmisc_1(B_162,C_163)) ) ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_838,plain,(
    ! [B_164,C_165] :
      ( ~ v1_xboole_0(B_164)
      | v1_xboole_0(k2_zfmisc_1(B_164,C_165)) ) ),
    inference(resolution,[status(thm)],[c_805,c_2])).

tff(c_842,plain,(
    ! [A_166,B_167,C_168] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_166,B_167))
      | v1_xboole_0(k3_zfmisc_1(A_166,B_167,C_168)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_838])).

tff(c_50,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_846,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_842,c_50])).

tff(c_885,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_882,c_846])).

tff(c_892,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_885])).

tff(c_893,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_377])).

tff(c_1029,plain,(
    ! [B_203,C_204] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_203,C_204))),B_203)
      | v1_xboole_0(k2_zfmisc_1(B_203,C_204)) ) ),
    inference(resolution,[status(thm)],[c_4,c_103])).

tff(c_1060,plain,(
    ! [B_203,C_204] :
      ( ~ v1_xboole_0(B_203)
      | v1_xboole_0(k2_zfmisc_1(B_203,C_204)) ) ),
    inference(resolution,[status(thm)],[c_1029,c_2])).

tff(c_1062,plain,(
    ! [B_205,C_206] :
      ( ~ v1_xboole_0(B_205)
      | v1_xboole_0(k2_zfmisc_1(B_205,C_206)) ) ),
    inference(resolution,[status(thm)],[c_1029,c_2])).

tff(c_1067,plain,(
    ! [A_207,B_208,C_209] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_207,B_208))
      | v1_xboole_0(k3_zfmisc_1(A_207,B_208,C_209)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1062])).

tff(c_1071,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1067,c_50])).

tff(c_1074,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1060,c_1071])).

tff(c_1081,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_1074])).

tff(c_1083,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1101,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1083,c_2])).

tff(c_1280,plain,(
    ! [A_244,B_245,C_246,D_247] :
      ( k7_mcart_1(A_244,B_245,C_246,D_247) = k2_mcart_1(D_247)
      | ~ m1_subset_1(D_247,k3_zfmisc_1(A_244,B_245,C_246))
      | k1_xboole_0 = C_246
      | k1_xboole_0 = B_245
      | k1_xboole_0 = A_244 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1284,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_1280])).

tff(c_1421,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1284])).

tff(c_1424,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1421,c_12])).

tff(c_1241,plain,(
    ! [C_240,A_241,B_242] :
      ( r2_hidden(C_240,A_241)
      | ~ r2_hidden(C_240,B_242)
      | ~ m1_subset_1(B_242,k1_zfmisc_1(A_241)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_1440,plain,(
    ! [A_264,A_265] :
      ( r2_hidden('#skF_1'(A_264),A_265)
      | ~ m1_subset_1(A_264,k1_zfmisc_1(A_265))
      | v1_xboole_0(A_264) ) ),
    inference(resolution,[status(thm)],[c_4,c_1241])).

tff(c_1474,plain,(
    ! [A_270,A_271] :
      ( ~ v1_xboole_0(A_270)
      | ~ m1_subset_1(A_271,k1_zfmisc_1(A_270))
      | v1_xboole_0(A_271) ) ),
    inference(resolution,[status(thm)],[c_1440,c_2])).

tff(c_1480,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_1474])).

tff(c_1488,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1424,c_1480])).

tff(c_1490,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1101,c_1488])).

tff(c_1492,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1384,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k6_mcart_1(A_257,B_258,C_259,D_260) = k2_mcart_1(k1_mcart_1(D_260))
      | ~ m1_subset_1(D_260,k3_zfmisc_1(A_257,B_258,C_259))
      | k1_xboole_0 = C_259
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_257 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1388,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_1384])).

tff(c_1504,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1492,c_1388])).

tff(c_1505,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1504])).

tff(c_1509,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_12])).

tff(c_1514,plain,(
    ! [A_273,A_274] :
      ( r2_hidden('#skF_1'(A_273),A_274)
      | ~ m1_subset_1(A_273,k1_zfmisc_1(A_274))
      | v1_xboole_0(A_273) ) ),
    inference(resolution,[status(thm)],[c_4,c_1241])).

tff(c_1550,plain,(
    ! [A_279,A_280] :
      ( ~ v1_xboole_0(A_279)
      | ~ m1_subset_1(A_280,k1_zfmisc_1(A_279))
      | v1_xboole_0(A_280) ) ),
    inference(resolution,[status(thm)],[c_1514,c_2])).

tff(c_1559,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_1550])).

tff(c_1567,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1509,c_1559])).

tff(c_1630,plain,(
    ! [B_289,C_290] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_289,C_290))),C_290)
      | v1_xboole_0(k2_zfmisc_1(B_289,C_290)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1178])).

tff(c_1659,plain,(
    ! [C_290,B_289] :
      ( ~ v1_xboole_0(C_290)
      | v1_xboole_0(k2_zfmisc_1(B_289,C_290)) ) ),
    inference(resolution,[status(thm)],[c_1630,c_2])).

tff(c_1139,plain,(
    ! [A_221,B_222,C_223] :
      ( r2_hidden(k1_mcart_1(A_221),B_222)
      | ~ r2_hidden(A_221,k2_zfmisc_1(B_222,C_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1685,plain,(
    ! [B_300,C_301] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_300,C_301))),B_300)
      | v1_xboole_0(k2_zfmisc_1(B_300,C_301)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1139])).

tff(c_1718,plain,(
    ! [B_302,C_303] :
      ( ~ v1_xboole_0(B_302)
      | v1_xboole_0(k2_zfmisc_1(B_302,C_303)) ) ),
    inference(resolution,[status(thm)],[c_1685,c_2])).

tff(c_1722,plain,(
    ! [A_304,B_305,C_306] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_304,B_305))
      | v1_xboole_0(k3_zfmisc_1(A_304,B_305,C_306)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1718])).

tff(c_1726,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1722,c_50])).

tff(c_1732,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1659,c_1726])).

tff(c_1737,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1567,c_1732])).

tff(c_1739,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1504])).

tff(c_1491,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitRight,[status(thm)],[c_1284])).

tff(c_1826,plain,
    ( k1_xboole_0 = '#skF_5'
    | k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(negUnitSimplification,[status(thm)],[c_1739,c_1491])).

tff(c_1827,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9') ),
    inference(splitLeft,[status(thm)],[c_1826])).

tff(c_1082,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7')
    | ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1103,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1082])).

tff(c_1829,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1827,c_1103])).

tff(c_1832,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1315,c_1829])).

tff(c_1833,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1826])).

tff(c_1841,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1833,c_12])).

tff(c_1843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1420,c_1841])).

tff(c_1844,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1082])).

tff(c_1927,plain,(
    ! [A_333,B_334,C_335] : k2_zfmisc_1(k2_zfmisc_1(A_333,B_334),C_335) = k3_zfmisc_1(A_333,B_334,C_335) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2017,plain,(
    ! [A_346,C_347,A_348,B_349] :
      ( r2_hidden(k2_mcart_1(A_346),C_347)
      | ~ r2_hidden(A_346,k3_zfmisc_1(A_348,B_349,C_347)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_20])).

tff(c_2032,plain,(
    r2_hidden(k2_mcart_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_2017])).

tff(c_2100,plain,(
    ! [A_353] :
      ( r2_hidden(k2_mcart_1('#skF_9'),A_353)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_353)) ) ),
    inference(resolution,[status(thm)],[c_2032,c_14])).

tff(c_2132,plain,(
    ! [A_358] :
      ( ~ v1_xboole_0(A_358)
      | ~ m1_subset_1('#skF_8',k1_zfmisc_1(A_358)) ) ),
    inference(resolution,[status(thm)],[c_2100,c_2])).

tff(c_2136,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_2132])).

tff(c_1978,plain,(
    ! [C_339,A_340,B_341] :
      ( r2_hidden(C_339,A_340)
      | ~ r2_hidden(C_339,B_341)
      | ~ m1_subset_1(B_341,k1_zfmisc_1(A_340)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2214,plain,(
    ! [A_364,A_365] :
      ( r2_hidden('#skF_1'(A_364),A_365)
      | ~ m1_subset_1(A_364,k1_zfmisc_1(A_365))
      | v1_xboole_0(A_364) ) ),
    inference(resolution,[status(thm)],[c_4,c_1978])).

tff(c_2246,plain,(
    ! [A_370,A_371] :
      ( ~ v1_xboole_0(A_370)
      | ~ m1_subset_1(A_371,k1_zfmisc_1(A_370))
      | v1_xboole_0(A_371) ) ),
    inference(resolution,[status(thm)],[c_2214,c_2])).

tff(c_2261,plain,
    ( ~ v1_xboole_0('#skF_4')
    | v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_2246])).

tff(c_2262,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2261])).

tff(c_2252,plain,
    ( ~ v1_xboole_0('#skF_3')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_40,c_2246])).

tff(c_2260,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1101,c_2252])).

tff(c_2127,plain,(
    ! [A_354,B_355,C_356,D_357] :
      ( k7_mcart_1(A_354,B_355,C_356,D_357) = k2_mcart_1(D_357)
      | ~ m1_subset_1(D_357,k3_zfmisc_1(A_354,B_355,C_356))
      | k1_xboole_0 = C_356
      | k1_xboole_0 = B_355
      | k1_xboole_0 = A_354 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2131,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') = k2_mcart_1('#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_2127])).

tff(c_2263,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2131])).

tff(c_2266,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2263,c_12])).

tff(c_2268,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2260,c_2266])).

tff(c_2270,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2131])).

tff(c_2241,plain,(
    ! [A_366,B_367,C_368,D_369] :
      ( k5_mcart_1(A_366,B_367,C_368,D_369) = k1_mcart_1(k1_mcart_1(D_369))
      | ~ m1_subset_1(D_369,k3_zfmisc_1(A_366,B_367,C_368))
      | k1_xboole_0 = C_368
      | k1_xboole_0 = B_367
      | k1_xboole_0 = A_366 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2245,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_2241])).

tff(c_2319,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_9')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2270,c_2245])).

tff(c_2320,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2319])).

tff(c_2325,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2320,c_12])).

tff(c_2327,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2262,c_2325])).

tff(c_2329,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2319])).

tff(c_2293,plain,(
    ! [A_374,B_375,C_376,D_377] :
      ( k6_mcart_1(A_374,B_375,C_376,D_377) = k2_mcart_1(k1_mcart_1(D_377))
      | ~ m1_subset_1(D_377,k3_zfmisc_1(A_374,B_375,C_376))
      | k1_xboole_0 = C_376
      | k1_xboole_0 = B_375
      | k1_xboole_0 = A_374 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2296,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_34,c_2293])).

tff(c_2299,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_2270,c_2296])).

tff(c_2510,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_2329,c_2299])).

tff(c_2511,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2510])).

tff(c_2517,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2511,c_12])).

tff(c_2519,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_2517])).

tff(c_2520,plain,(
    k2_mcart_1(k1_mcart_1('#skF_9')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9') ),
    inference(splitRight,[status(thm)],[c_2510])).

tff(c_2652,plain,(
    ! [A_429,A_430,B_431,C_432] :
      ( r2_hidden(k1_mcart_1(A_429),k2_zfmisc_1(A_430,B_431))
      | ~ r2_hidden(A_429,k3_zfmisc_1(A_430,B_431,C_432)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1927,c_22])).

tff(c_2702,plain,(
    r2_hidden(k1_mcart_1('#skF_9'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_2652])).

tff(c_2706,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2702,c_20])).

tff(c_2719,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_9'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2520,c_2706])).

tff(c_2721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1844,c_2719])).

tff(c_2722,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2261])).

tff(c_1918,plain,(
    ! [A_330,C_331,B_332] :
      ( r2_hidden(k2_mcart_1(A_330),C_331)
      | ~ r2_hidden(A_330,k2_zfmisc_1(B_332,C_331)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2885,plain,(
    ! [B_457,C_458] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_457,C_458))),C_458)
      | v1_xboole_0(k2_zfmisc_1(B_457,C_458)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1918])).

tff(c_2916,plain,(
    ! [C_459,B_460] :
      ( ~ v1_xboole_0(C_459)
      | v1_xboole_0(k2_zfmisc_1(B_460,C_459)) ) ),
    inference(resolution,[status(thm)],[c_2885,c_2])).

tff(c_1893,plain,(
    ! [A_324,B_325,C_326] :
      ( r2_hidden(k1_mcart_1(A_324),B_325)
      | ~ r2_hidden(A_324,k2_zfmisc_1(B_325,C_326)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_2838,plain,(
    ! [B_450,C_451] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_450,C_451))),B_450)
      | v1_xboole_0(k2_zfmisc_1(B_450,C_451)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1893])).

tff(c_2871,plain,(
    ! [B_452,C_453] :
      ( ~ v1_xboole_0(B_452)
      | v1_xboole_0(k2_zfmisc_1(B_452,C_453)) ) ),
    inference(resolution,[status(thm)],[c_2838,c_2])).

tff(c_2875,plain,(
    ! [A_454,B_455,C_456] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_454,B_455))
      | v1_xboole_0(k3_zfmisc_1(A_454,B_455,C_456)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_2871])).

tff(c_2879,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2875,c_50])).

tff(c_2919,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2916,c_2879])).

tff(c_2926,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2722,c_2919])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:41:14 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.51/1.78  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.80  
% 4.51/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.51/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2
% 4.51/1.80  
% 4.51/1.80  %Foreground sorts:
% 4.51/1.80  
% 4.51/1.80  
% 4.51/1.80  %Background operators:
% 4.51/1.80  
% 4.51/1.80  
% 4.51/1.80  %Foreground operators:
% 4.51/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.51/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.51/1.80  tff('#skF_1', type, '#skF_1': $i > $i).
% 4.51/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.51/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.51/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.51/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.51/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.51/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.51/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.51/1.80  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.80  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.51/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.51/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.51/1.80  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.51/1.80  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.51/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.51/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.51/1.80  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.51/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.51/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.51/1.80  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.51/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.51/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.51/1.80  
% 4.69/1.82  tff(f_99, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 4.69/1.82  tff(f_53, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 4.69/1.82  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 4.69/1.82  tff(f_46, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (r2_hidden(C, B) => r2_hidden(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_subset_1)).
% 4.69/1.82  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 4.69/1.82  tff(f_79, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.69/1.82  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 4.69/1.82  tff(c_36, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_32, plain, (r2_hidden('#skF_9', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_18, plain, (![A_16, B_17, C_18]: (k2_zfmisc_1(k2_zfmisc_1(A_16, B_17), C_18)=k3_zfmisc_1(A_16, B_17, C_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.82  tff(c_1178, plain, (![A_230, C_231, B_232]: (r2_hidden(k2_mcart_1(A_230), C_231) | ~r2_hidden(A_230, k2_zfmisc_1(B_232, C_231)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_1296, plain, (![A_249, C_250, A_251, B_252]: (r2_hidden(k2_mcart_1(A_249), C_250) | ~r2_hidden(A_249, k3_zfmisc_1(A_251, B_252, C_250)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1178])).
% 4.69/1.82  tff(c_1315, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_32, c_1296])).
% 4.69/1.82  tff(c_14, plain, (![C_13, A_10, B_11]: (r2_hidden(C_13, A_10) | ~r2_hidden(C_13, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.69/1.82  tff(c_1389, plain, (![A_261]: (r2_hidden(k2_mcart_1('#skF_9'), A_261) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_261)))), inference(resolution, [status(thm)], [c_1315, c_14])).
% 4.69/1.82  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.82  tff(c_1416, plain, (![A_262]: (~v1_xboole_0(A_262) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_262)))), inference(resolution, [status(thm)], [c_1389, c_2])).
% 4.69/1.82  tff(c_1420, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_1416])).
% 4.69/1.82  tff(c_122, plain, (![A_62, B_63, C_64]: (k2_zfmisc_1(k2_zfmisc_1(A_62, B_63), C_64)=k3_zfmisc_1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.82  tff(c_20, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_206, plain, (![A_75, C_76, A_77, B_78]: (r2_hidden(k2_mcart_1(A_75), C_76) | ~r2_hidden(A_75, k3_zfmisc_1(A_77, B_78, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_20])).
% 4.69/1.82  tff(c_221, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_32, c_206])).
% 4.69/1.82  tff(c_294, plain, (![A_86]: (r2_hidden(k2_mcart_1('#skF_9'), A_86) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_86)))), inference(resolution, [status(thm)], [c_221, c_14])).
% 4.69/1.82  tff(c_321, plain, (![A_87]: (~v1_xboole_0(A_87) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_294, c_2])).
% 4.69/1.82  tff(c_325, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_321])).
% 4.69/1.82  tff(c_30, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8') | ~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_51, plain, (~r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitLeft, [status(thm)], [c_30])).
% 4.69/1.82  tff(c_38, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.69/1.82  tff(c_170, plain, (![C_69, A_70, B_71]: (r2_hidden(C_69, A_70) | ~r2_hidden(C_69, B_71) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.69/1.82  tff(c_338, plain, (![A_90, A_91]: (r2_hidden('#skF_1'(A_90), A_91) | ~m1_subset_1(A_90, k1_zfmisc_1(A_91)) | v1_xboole_0(A_90))), inference(resolution, [status(thm)], [c_4, c_170])).
% 4.69/1.82  tff(c_365, plain, (![A_92, A_93]: (~v1_xboole_0(A_92) | ~m1_subset_1(A_93, k1_zfmisc_1(A_92)) | v1_xboole_0(A_93))), inference(resolution, [status(thm)], [c_338, c_2])).
% 4.69/1.82  tff(c_378, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_365])).
% 4.69/1.82  tff(c_385, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_378])).
% 4.69/1.82  tff(c_40, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_377, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_365])).
% 4.69/1.82  tff(c_379, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_377])).
% 4.69/1.82  tff(c_34, plain, (m1_subset_1('#skF_9', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.69/1.82  tff(c_289, plain, (![A_82, B_83, C_84, D_85]: (k7_mcart_1(A_82, B_83, C_84, D_85)=k2_mcart_1(D_85) | ~m1_subset_1(D_85, k3_zfmisc_1(A_82, B_83, C_84)) | k1_xboole_0=C_84 | k1_xboole_0=B_83 | k1_xboole_0=A_82)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.82  tff(c_293, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_289])).
% 4.69/1.82  tff(c_386, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_293])).
% 4.69/1.82  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.69/1.82  tff(c_389, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_386, c_12])).
% 4.69/1.82  tff(c_391, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_389])).
% 4.69/1.82  tff(c_393, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_293])).
% 4.69/1.82  tff(c_380, plain, (![A_94, B_95, C_96, D_97]: (k5_mcart_1(A_94, B_95, C_96, D_97)=k1_mcart_1(k1_mcart_1(D_97)) | ~m1_subset_1(D_97, k3_zfmisc_1(A_94, B_95, C_96)) | k1_xboole_0=C_96 | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.82  tff(c_384, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_380])).
% 4.69/1.82  tff(c_467, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_393, c_384])).
% 4.69/1.82  tff(c_468, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_467])).
% 4.69/1.82  tff(c_473, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_468, c_12])).
% 4.69/1.82  tff(c_475, plain, $false, inference(negUnitSimplification, [status(thm)], [c_385, c_473])).
% 4.69/1.82  tff(c_476, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_467])).
% 4.69/1.82  tff(c_491, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitLeft, [status(thm)], [c_476])).
% 4.69/1.82  tff(c_22, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_670, plain, (![A_145, A_146, B_147, C_148]: (r2_hidden(k1_mcart_1(A_145), k2_zfmisc_1(A_146, B_147)) | ~r2_hidden(A_145, k3_zfmisc_1(A_146, B_147, C_148)))), inference(superposition, [status(thm), theory('equality')], [c_122, c_22])).
% 4.69/1.82  tff(c_712, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_670])).
% 4.69/1.82  tff(c_718, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_9')), '#skF_6')), inference(resolution, [status(thm)], [c_712, c_22])).
% 4.69/1.82  tff(c_730, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_491, c_718])).
% 4.69/1.82  tff(c_732, plain, $false, inference(negUnitSimplification, [status(thm)], [c_51, c_730])).
% 4.69/1.82  tff(c_733, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_476])).
% 4.69/1.82  tff(c_740, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_12])).
% 4.69/1.82  tff(c_742, plain, $false, inference(negUnitSimplification, [status(thm)], [c_325, c_740])).
% 4.69/1.82  tff(c_743, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_378])).
% 4.69/1.82  tff(c_94, plain, (![A_53, C_54, B_55]: (r2_hidden(k2_mcart_1(A_53), C_54) | ~r2_hidden(A_53, k2_zfmisc_1(B_55, C_54)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_847, plain, (![B_169, C_170]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_169, C_170))), C_170) | v1_xboole_0(k2_zfmisc_1(B_169, C_170)))), inference(resolution, [status(thm)], [c_4, c_94])).
% 4.69/1.82  tff(c_882, plain, (![C_171, B_172]: (~v1_xboole_0(C_171) | v1_xboole_0(k2_zfmisc_1(B_172, C_171)))), inference(resolution, [status(thm)], [c_847, c_2])).
% 4.69/1.82  tff(c_103, plain, (![A_56, B_57, C_58]: (r2_hidden(k1_mcart_1(A_56), B_57) | ~r2_hidden(A_56, k2_zfmisc_1(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_805, plain, (![B_162, C_163]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_162, C_163))), B_162) | v1_xboole_0(k2_zfmisc_1(B_162, C_163)))), inference(resolution, [status(thm)], [c_4, c_103])).
% 4.69/1.82  tff(c_838, plain, (![B_164, C_165]: (~v1_xboole_0(B_164) | v1_xboole_0(k2_zfmisc_1(B_164, C_165)))), inference(resolution, [status(thm)], [c_805, c_2])).
% 4.69/1.82  tff(c_842, plain, (![A_166, B_167, C_168]: (~v1_xboole_0(k2_zfmisc_1(A_166, B_167)) | v1_xboole_0(k3_zfmisc_1(A_166, B_167, C_168)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_838])).
% 4.69/1.82  tff(c_50, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_32, c_2])).
% 4.69/1.82  tff(c_846, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_842, c_50])).
% 4.69/1.82  tff(c_885, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_882, c_846])).
% 4.69/1.82  tff(c_892, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_743, c_885])).
% 4.69/1.82  tff(c_893, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_377])).
% 4.69/1.82  tff(c_1029, plain, (![B_203, C_204]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_203, C_204))), B_203) | v1_xboole_0(k2_zfmisc_1(B_203, C_204)))), inference(resolution, [status(thm)], [c_4, c_103])).
% 4.69/1.82  tff(c_1060, plain, (![B_203, C_204]: (~v1_xboole_0(B_203) | v1_xboole_0(k2_zfmisc_1(B_203, C_204)))), inference(resolution, [status(thm)], [c_1029, c_2])).
% 4.69/1.82  tff(c_1062, plain, (![B_205, C_206]: (~v1_xboole_0(B_205) | v1_xboole_0(k2_zfmisc_1(B_205, C_206)))), inference(resolution, [status(thm)], [c_1029, c_2])).
% 4.69/1.82  tff(c_1067, plain, (![A_207, B_208, C_209]: (~v1_xboole_0(k2_zfmisc_1(A_207, B_208)) | v1_xboole_0(k3_zfmisc_1(A_207, B_208, C_209)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1062])).
% 4.69/1.82  tff(c_1071, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1067, c_50])).
% 4.69/1.82  tff(c_1074, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1060, c_1071])).
% 4.69/1.82  tff(c_1081, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_1074])).
% 4.69/1.82  tff(c_1083, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 4.69/1.82  tff(c_1101, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1083, c_2])).
% 4.69/1.82  tff(c_1280, plain, (![A_244, B_245, C_246, D_247]: (k7_mcart_1(A_244, B_245, C_246, D_247)=k2_mcart_1(D_247) | ~m1_subset_1(D_247, k3_zfmisc_1(A_244, B_245, C_246)) | k1_xboole_0=C_246 | k1_xboole_0=B_245 | k1_xboole_0=A_244)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.82  tff(c_1284, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_1280])).
% 4.69/1.82  tff(c_1421, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1284])).
% 4.69/1.82  tff(c_1424, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1421, c_12])).
% 4.69/1.82  tff(c_1241, plain, (![C_240, A_241, B_242]: (r2_hidden(C_240, A_241) | ~r2_hidden(C_240, B_242) | ~m1_subset_1(B_242, k1_zfmisc_1(A_241)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.69/1.82  tff(c_1440, plain, (![A_264, A_265]: (r2_hidden('#skF_1'(A_264), A_265) | ~m1_subset_1(A_264, k1_zfmisc_1(A_265)) | v1_xboole_0(A_264))), inference(resolution, [status(thm)], [c_4, c_1241])).
% 4.69/1.82  tff(c_1474, plain, (![A_270, A_271]: (~v1_xboole_0(A_270) | ~m1_subset_1(A_271, k1_zfmisc_1(A_270)) | v1_xboole_0(A_271))), inference(resolution, [status(thm)], [c_1440, c_2])).
% 4.69/1.82  tff(c_1480, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_1474])).
% 4.69/1.82  tff(c_1488, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1424, c_1480])).
% 4.69/1.82  tff(c_1490, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1101, c_1488])).
% 4.69/1.82  tff(c_1492, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1284])).
% 4.69/1.82  tff(c_1384, plain, (![A_257, B_258, C_259, D_260]: (k6_mcart_1(A_257, B_258, C_259, D_260)=k2_mcart_1(k1_mcart_1(D_260)) | ~m1_subset_1(D_260, k3_zfmisc_1(A_257, B_258, C_259)) | k1_xboole_0=C_259 | k1_xboole_0=B_258 | k1_xboole_0=A_257)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.82  tff(c_1388, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_1384])).
% 4.69/1.82  tff(c_1504, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1492, c_1388])).
% 4.69/1.82  tff(c_1505, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1504])).
% 4.69/1.82  tff(c_1509, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_12])).
% 4.69/1.82  tff(c_1514, plain, (![A_273, A_274]: (r2_hidden('#skF_1'(A_273), A_274) | ~m1_subset_1(A_273, k1_zfmisc_1(A_274)) | v1_xboole_0(A_273))), inference(resolution, [status(thm)], [c_4, c_1241])).
% 4.69/1.82  tff(c_1550, plain, (![A_279, A_280]: (~v1_xboole_0(A_279) | ~m1_subset_1(A_280, k1_zfmisc_1(A_279)) | v1_xboole_0(A_280))), inference(resolution, [status(thm)], [c_1514, c_2])).
% 4.69/1.82  tff(c_1559, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_1550])).
% 4.69/1.82  tff(c_1567, plain, (v1_xboole_0('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1509, c_1559])).
% 4.69/1.82  tff(c_1630, plain, (![B_289, C_290]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_289, C_290))), C_290) | v1_xboole_0(k2_zfmisc_1(B_289, C_290)))), inference(resolution, [status(thm)], [c_4, c_1178])).
% 4.69/1.82  tff(c_1659, plain, (![C_290, B_289]: (~v1_xboole_0(C_290) | v1_xboole_0(k2_zfmisc_1(B_289, C_290)))), inference(resolution, [status(thm)], [c_1630, c_2])).
% 4.69/1.82  tff(c_1139, plain, (![A_221, B_222, C_223]: (r2_hidden(k1_mcart_1(A_221), B_222) | ~r2_hidden(A_221, k2_zfmisc_1(B_222, C_223)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.82  tff(c_1685, plain, (![B_300, C_301]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_300, C_301))), B_300) | v1_xboole_0(k2_zfmisc_1(B_300, C_301)))), inference(resolution, [status(thm)], [c_4, c_1139])).
% 4.69/1.82  tff(c_1718, plain, (![B_302, C_303]: (~v1_xboole_0(B_302) | v1_xboole_0(k2_zfmisc_1(B_302, C_303)))), inference(resolution, [status(thm)], [c_1685, c_2])).
% 4.69/1.82  tff(c_1722, plain, (![A_304, B_305, C_306]: (~v1_xboole_0(k2_zfmisc_1(A_304, B_305)) | v1_xboole_0(k3_zfmisc_1(A_304, B_305, C_306)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1718])).
% 4.69/1.82  tff(c_1726, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1722, c_50])).
% 4.69/1.82  tff(c_1732, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1659, c_1726])).
% 4.69/1.82  tff(c_1737, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1567, c_1732])).
% 4.69/1.82  tff(c_1739, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1504])).
% 4.69/1.82  tff(c_1491, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitRight, [status(thm)], [c_1284])).
% 4.69/1.82  tff(c_1826, plain, (k1_xboole_0='#skF_5' | k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(negUnitSimplification, [status(thm)], [c_1739, c_1491])).
% 4.69/1.82  tff(c_1827, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9')), inference(splitLeft, [status(thm)], [c_1826])).
% 4.69/1.82  tff(c_1082, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7') | ~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_30])).
% 4.69/1.82  tff(c_1103, plain, (~r2_hidden(k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_8')), inference(splitLeft, [status(thm)], [c_1082])).
% 4.69/1.82  tff(c_1829, plain, (~r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1827, c_1103])).
% 4.69/1.82  tff(c_1832, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1315, c_1829])).
% 4.69/1.82  tff(c_1833, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_1826])).
% 4.69/1.82  tff(c_1841, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1833, c_12])).
% 4.69/1.82  tff(c_1843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1420, c_1841])).
% 4.69/1.82  tff(c_1844, plain, (~r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(splitRight, [status(thm)], [c_1082])).
% 4.69/1.82  tff(c_1927, plain, (![A_333, B_334, C_335]: (k2_zfmisc_1(k2_zfmisc_1(A_333, B_334), C_335)=k3_zfmisc_1(A_333, B_334, C_335))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.69/1.82  tff(c_2017, plain, (![A_346, C_347, A_348, B_349]: (r2_hidden(k2_mcart_1(A_346), C_347) | ~r2_hidden(A_346, k3_zfmisc_1(A_348, B_349, C_347)))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_20])).
% 4.69/1.82  tff(c_2032, plain, (r2_hidden(k2_mcart_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_32, c_2017])).
% 4.69/1.82  tff(c_2100, plain, (![A_353]: (r2_hidden(k2_mcart_1('#skF_9'), A_353) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_353)))), inference(resolution, [status(thm)], [c_2032, c_14])).
% 4.69/1.82  tff(c_2132, plain, (![A_358]: (~v1_xboole_0(A_358) | ~m1_subset_1('#skF_8', k1_zfmisc_1(A_358)))), inference(resolution, [status(thm)], [c_2100, c_2])).
% 4.69/1.82  tff(c_2136, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_36, c_2132])).
% 4.69/1.82  tff(c_1978, plain, (![C_339, A_340, B_341]: (r2_hidden(C_339, A_340) | ~r2_hidden(C_339, B_341) | ~m1_subset_1(B_341, k1_zfmisc_1(A_340)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 4.69/1.83  tff(c_2214, plain, (![A_364, A_365]: (r2_hidden('#skF_1'(A_364), A_365) | ~m1_subset_1(A_364, k1_zfmisc_1(A_365)) | v1_xboole_0(A_364))), inference(resolution, [status(thm)], [c_4, c_1978])).
% 4.69/1.83  tff(c_2246, plain, (![A_370, A_371]: (~v1_xboole_0(A_370) | ~m1_subset_1(A_371, k1_zfmisc_1(A_370)) | v1_xboole_0(A_371))), inference(resolution, [status(thm)], [c_2214, c_2])).
% 4.69/1.83  tff(c_2261, plain, (~v1_xboole_0('#skF_4') | v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_38, c_2246])).
% 4.69/1.83  tff(c_2262, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_2261])).
% 4.69/1.83  tff(c_2252, plain, (~v1_xboole_0('#skF_3') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_40, c_2246])).
% 4.69/1.83  tff(c_2260, plain, (~v1_xboole_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1101, c_2252])).
% 4.69/1.83  tff(c_2127, plain, (![A_354, B_355, C_356, D_357]: (k7_mcart_1(A_354, B_355, C_356, D_357)=k2_mcart_1(D_357) | ~m1_subset_1(D_357, k3_zfmisc_1(A_354, B_355, C_356)) | k1_xboole_0=C_356 | k1_xboole_0=B_355 | k1_xboole_0=A_354)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.83  tff(c_2131, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')=k2_mcart_1('#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_2127])).
% 4.69/1.83  tff(c_2263, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_2131])).
% 4.69/1.83  tff(c_2266, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2263, c_12])).
% 4.69/1.83  tff(c_2268, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2260, c_2266])).
% 4.69/1.83  tff(c_2270, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_2131])).
% 4.69/1.83  tff(c_2241, plain, (![A_366, B_367, C_368, D_369]: (k5_mcart_1(A_366, B_367, C_368, D_369)=k1_mcart_1(k1_mcart_1(D_369)) | ~m1_subset_1(D_369, k3_zfmisc_1(A_366, B_367, C_368)) | k1_xboole_0=C_368 | k1_xboole_0=B_367 | k1_xboole_0=A_366)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.83  tff(c_2245, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_2241])).
% 4.69/1.83  tff(c_2319, plain, (k1_mcart_1(k1_mcart_1('#skF_9'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2270, c_2245])).
% 4.69/1.83  tff(c_2320, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_2319])).
% 4.69/1.83  tff(c_2325, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2320, c_12])).
% 4.69/1.83  tff(c_2327, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2262, c_2325])).
% 4.69/1.83  tff(c_2329, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_2319])).
% 4.69/1.83  tff(c_2293, plain, (![A_374, B_375, C_376, D_377]: (k6_mcart_1(A_374, B_375, C_376, D_377)=k2_mcart_1(k1_mcart_1(D_377)) | ~m1_subset_1(D_377, k3_zfmisc_1(A_374, B_375, C_376)) | k1_xboole_0=C_376 | k1_xboole_0=B_375 | k1_xboole_0=A_374)), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.69/1.83  tff(c_2296, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_34, c_2293])).
% 4.69/1.83  tff(c_2299, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_2270, c_2296])).
% 4.69/1.83  tff(c_2510, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_2329, c_2299])).
% 4.69/1.83  tff(c_2511, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2510])).
% 4.69/1.83  tff(c_2517, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2511, c_12])).
% 4.69/1.83  tff(c_2519, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2136, c_2517])).
% 4.69/1.83  tff(c_2520, plain, (k2_mcart_1(k1_mcart_1('#skF_9'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9')), inference(splitRight, [status(thm)], [c_2510])).
% 4.69/1.83  tff(c_2652, plain, (![A_429, A_430, B_431, C_432]: (r2_hidden(k1_mcart_1(A_429), k2_zfmisc_1(A_430, B_431)) | ~r2_hidden(A_429, k3_zfmisc_1(A_430, B_431, C_432)))), inference(superposition, [status(thm), theory('equality')], [c_1927, c_22])).
% 4.69/1.83  tff(c_2702, plain, (r2_hidden(k1_mcart_1('#skF_9'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_2652])).
% 4.69/1.83  tff(c_2706, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_9')), '#skF_7')), inference(resolution, [status(thm)], [c_2702, c_20])).
% 4.69/1.83  tff(c_2719, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_9'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2520, c_2706])).
% 4.69/1.83  tff(c_2721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1844, c_2719])).
% 4.69/1.83  tff(c_2722, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_2261])).
% 4.69/1.83  tff(c_1918, plain, (![A_330, C_331, B_332]: (r2_hidden(k2_mcart_1(A_330), C_331) | ~r2_hidden(A_330, k2_zfmisc_1(B_332, C_331)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.83  tff(c_2885, plain, (![B_457, C_458]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_457, C_458))), C_458) | v1_xboole_0(k2_zfmisc_1(B_457, C_458)))), inference(resolution, [status(thm)], [c_4, c_1918])).
% 4.69/1.83  tff(c_2916, plain, (![C_459, B_460]: (~v1_xboole_0(C_459) | v1_xboole_0(k2_zfmisc_1(B_460, C_459)))), inference(resolution, [status(thm)], [c_2885, c_2])).
% 4.69/1.83  tff(c_1893, plain, (![A_324, B_325, C_326]: (r2_hidden(k1_mcart_1(A_324), B_325) | ~r2_hidden(A_324, k2_zfmisc_1(B_325, C_326)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.69/1.83  tff(c_2838, plain, (![B_450, C_451]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_450, C_451))), B_450) | v1_xboole_0(k2_zfmisc_1(B_450, C_451)))), inference(resolution, [status(thm)], [c_4, c_1893])).
% 4.69/1.83  tff(c_2871, plain, (![B_452, C_453]: (~v1_xboole_0(B_452) | v1_xboole_0(k2_zfmisc_1(B_452, C_453)))), inference(resolution, [status(thm)], [c_2838, c_2])).
% 4.69/1.83  tff(c_2875, plain, (![A_454, B_455, C_456]: (~v1_xboole_0(k2_zfmisc_1(A_454, B_455)) | v1_xboole_0(k3_zfmisc_1(A_454, B_455, C_456)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_2871])).
% 4.69/1.83  tff(c_2879, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2875, c_50])).
% 4.69/1.83  tff(c_2919, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_2916, c_2879])).
% 4.69/1.83  tff(c_2926, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2722, c_2919])).
% 4.69/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.83  
% 4.69/1.83  Inference rules
% 4.69/1.83  ----------------------
% 4.69/1.83  #Ref     : 0
% 4.69/1.83  #Sup     : 658
% 4.69/1.83  #Fact    : 0
% 4.69/1.83  #Define  : 0
% 4.69/1.83  #Split   : 27
% 4.69/1.83  #Chain   : 0
% 4.69/1.83  #Close   : 0
% 4.69/1.83  
% 4.69/1.83  Ordering : KBO
% 4.69/1.83  
% 4.69/1.83  Simplification rules
% 4.69/1.83  ----------------------
% 4.69/1.83  #Subsume      : 132
% 4.69/1.83  #Demod        : 229
% 4.69/1.83  #Tautology    : 63
% 4.69/1.83  #SimpNegUnit  : 37
% 4.69/1.83  #BackRed      : 72
% 4.69/1.83  
% 4.69/1.83  #Partial instantiations: 0
% 4.69/1.83  #Strategies tried      : 1
% 4.69/1.83  
% 4.69/1.83  Timing (in seconds)
% 4.69/1.83  ----------------------
% 4.69/1.83  Preprocessing        : 0.31
% 4.69/1.83  Parsing              : 0.16
% 4.69/1.83  CNF conversion       : 0.03
% 4.69/1.83  Main loop            : 0.74
% 4.69/1.83  Inferencing          : 0.26
% 4.69/1.83  Reduction            : 0.21
% 4.69/1.83  Demodulation         : 0.13
% 4.69/1.83  BG Simplification    : 0.03
% 4.69/1.83  Subsumption          : 0.17
% 4.69/1.83  Abstraction          : 0.04
% 4.69/1.83  MUC search           : 0.00
% 4.69/1.83  Cooper               : 0.00
% 4.69/1.83  Total                : 1.11
% 4.69/1.83  Index Insertion      : 0.00
% 4.69/1.83  Index Deletion       : 0.00
% 4.69/1.83  Index Matching       : 0.00
% 4.69/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
