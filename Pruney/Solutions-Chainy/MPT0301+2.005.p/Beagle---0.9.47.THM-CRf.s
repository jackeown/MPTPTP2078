%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:40 EST 2020

% Result     : Theorem 6.94s
% Output     : CNFRefutation 6.94s
% Verified   : 
% Statistics : Number of formulae       :  158 ( 580 expanded)
%              Number of leaves         :   37 ( 187 expanded)
%              Depth                    :   12
%              Number of atoms          :  193 (1089 expanded)
%              Number of equality atoms :   85 ( 795 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_89,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_62,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_171,plain,(
    k1_xboole_0 != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_83,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_197,plain,(
    ! [A_94,B_95,C_96] :
      ( ~ r1_xboole_0(A_94,B_95)
      | ~ r2_hidden(C_96,k3_xboole_0(A_94,B_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_203,plain,(
    ! [A_97,B_98] :
      ( ~ r1_xboole_0(A_97,B_98)
      | k3_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_208,plain,(
    ! [A_99] : k3_xboole_0(A_99,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_203])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [A_99,C_7] :
      ( ~ r1_xboole_0(A_99,k1_xboole_0)
      | ~ r2_hidden(C_7,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_6])).

tff(c_218,plain,(
    ! [C_7] : ~ r2_hidden(C_7,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_72,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_191,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_719,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( r2_hidden(k4_tarski(A_136,B_137),k2_zfmisc_1(C_138,D_139))
      | ~ r2_hidden(B_137,D_139)
      | ~ r2_hidden(A_136,C_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_728,plain,(
    ! [A_136,B_137] :
      ( r2_hidden(k4_tarski(A_136,B_137),k1_xboole_0)
      | ~ r2_hidden(B_137,'#skF_12')
      | ~ r2_hidden(A_136,'#skF_11') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_719])).

tff(c_731,plain,(
    ! [B_137,A_136] :
      ( ~ r2_hidden(B_137,'#skF_12')
      | ~ r2_hidden(A_136,'#skF_11') ) ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_728])).

tff(c_733,plain,(
    ! [A_140] : ~ r2_hidden(A_140,'#skF_11') ),
    inference(splitLeft,[status(thm)],[c_731])).

tff(c_737,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_8,c_733])).

tff(c_741,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_737])).

tff(c_743,plain,(
    ! [B_141] : ~ r2_hidden(B_141,'#skF_12') ),
    inference(splitRight,[status(thm)],[c_731])).

tff(c_747,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(resolution,[status(thm)],[c_8,c_743])).

tff(c_751,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_747])).

tff(c_752,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_754,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_752])).

tff(c_757,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_8])).

tff(c_2813,plain,(
    ! [A_217,B_218,D_219] :
      ( r2_hidden('#skF_8'(A_217,B_218,k2_zfmisc_1(A_217,B_218),D_219),B_218)
      | ~ r2_hidden(D_219,k2_zfmisc_1(A_217,B_218)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_760,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_12])).

tff(c_834,plain,(
    ! [A_146,B_147,C_148] :
      ( ~ r1_xboole_0(A_146,B_147)
      | ~ r2_hidden(C_148,k3_xboole_0(A_146,B_147)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_849,plain,(
    ! [A_152,B_153] :
      ( ~ r1_xboole_0(A_152,B_153)
      | k3_xboole_0(A_152,B_153) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_757,c_834])).

tff(c_854,plain,(
    ! [A_154] : k3_xboole_0(A_154,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_760,c_849])).

tff(c_859,plain,(
    ! [A_154,C_7] :
      ( ~ r1_xboole_0(A_154,'#skF_10')
      | ~ r2_hidden(C_7,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_6])).

tff(c_864,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_760,c_859])).

tff(c_2828,plain,(
    ! [D_220,A_221] : ~ r2_hidden(D_220,k2_zfmisc_1(A_221,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_2813,c_864])).

tff(c_2851,plain,(
    ! [A_221] : k2_zfmisc_1(A_221,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_757,c_2828])).

tff(c_70,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0
    | k2_zfmisc_1('#skF_11','#skF_12') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_789,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_754,c_754,c_70])).

tff(c_790,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_789])).

tff(c_2855,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2851,c_790])).

tff(c_2856,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_789])).

tff(c_753,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_2867,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2856,c_754,c_753])).

tff(c_2868,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_752])).

tff(c_5174,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_753])).

tff(c_2872,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_8])).

tff(c_5128,plain,(
    ! [A_298,B_299,D_300] :
      ( r2_hidden('#skF_7'(A_298,B_299,k2_zfmisc_1(A_298,B_299),D_300),A_298)
      | ~ r2_hidden(D_300,k2_zfmisc_1(A_298,B_299)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2875,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_12])).

tff(c_2949,plain,(
    ! [A_226,B_227,C_228] :
      ( ~ r1_xboole_0(A_226,B_227)
      | ~ r2_hidden(C_228,k3_xboole_0(A_226,B_227)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2956,plain,(
    ! [A_229,B_230] :
      ( ~ r1_xboole_0(A_229,B_230)
      | k3_xboole_0(A_229,B_230) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_2872,c_2949])).

tff(c_2961,plain,(
    ! [A_231] : k3_xboole_0(A_231,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2875,c_2956])).

tff(c_2966,plain,(
    ! [A_231,C_7] :
      ( ~ r1_xboole_0(A_231,'#skF_9')
      | ~ r2_hidden(C_7,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2961,c_6])).

tff(c_2971,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_2966])).

tff(c_5143,plain,(
    ! [D_301,B_302] : ~ r2_hidden(D_301,k2_zfmisc_1('#skF_9',B_302)) ),
    inference(resolution,[status(thm)],[c_5128,c_2971])).

tff(c_5166,plain,(
    ! [B_302] : k2_zfmisc_1('#skF_9',B_302) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2872,c_5143])).

tff(c_2881,plain,
    ( k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9'
    | k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2868,c_2868,c_70])).

tff(c_2882,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_2881])).

tff(c_5170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5166,c_2882])).

tff(c_5171,plain,(
    k2_zfmisc_1('#skF_11','#skF_12') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_2881])).

tff(c_5179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5174,c_5171])).

tff(c_5181,plain,(
    k1_xboole_0 = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5183,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_12' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5181,c_8])).

tff(c_9026,plain,(
    ! [A_448,B_449,D_450] :
      ( r2_hidden('#skF_8'(A_448,B_449,k2_zfmisc_1(A_448,B_449),D_450),B_449)
      | ~ r2_hidden(D_450,k2_zfmisc_1(A_448,B_449)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5186,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5181,c_12])).

tff(c_6898,plain,(
    ! [A_382,B_383,C_384] :
      ( ~ r1_xboole_0(A_382,B_383)
      | ~ r2_hidden(C_384,k3_xboole_0(A_382,B_383)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6904,plain,(
    ! [A_385,B_386] :
      ( ~ r1_xboole_0(A_385,B_386)
      | k3_xboole_0(A_385,B_386) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_5183,c_6898])).

tff(c_6909,plain,(
    ! [A_387] : k3_xboole_0(A_387,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5186,c_6904])).

tff(c_6914,plain,(
    ! [A_387,C_7] :
      ( ~ r1_xboole_0(A_387,'#skF_12')
      | ~ r2_hidden(C_7,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6909,c_6])).

tff(c_6919,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_6914])).

tff(c_9037,plain,(
    ! [D_451,A_452] : ~ r2_hidden(D_451,k2_zfmisc_1(A_452,'#skF_12')) ),
    inference(resolution,[status(thm)],[c_9026,c_6919])).

tff(c_9052,plain,(
    ! [A_452] : k2_zfmisc_1(A_452,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5183,c_9037])).

tff(c_6839,plain,(
    ! [A_372,B_373,D_374] :
      ( r2_hidden('#skF_7'(A_372,B_373,k2_zfmisc_1(A_372,B_373),D_374),A_372)
      | ~ r2_hidden(D_374,k2_zfmisc_1(A_372,B_373)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5289,plain,(
    ! [A_312,B_313,C_314] :
      ( ~ r1_xboole_0(A_312,B_313)
      | ~ r2_hidden(C_314,k3_xboole_0(A_312,B_313)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_5295,plain,(
    ! [A_315,B_316] :
      ( ~ r1_xboole_0(A_315,B_316)
      | k3_xboole_0(A_315,B_316) = '#skF_12' ) ),
    inference(resolution,[status(thm)],[c_5183,c_5289])).

tff(c_5300,plain,(
    ! [A_317] : k3_xboole_0(A_317,'#skF_12') = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5186,c_5295])).

tff(c_5305,plain,(
    ! [A_317,C_7] :
      ( ~ r1_xboole_0(A_317,'#skF_12')
      | ~ r2_hidden(C_7,'#skF_12') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5300,c_6])).

tff(c_5310,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_12') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5186,c_5305])).

tff(c_6850,plain,(
    ! [D_375,B_376] : ~ r2_hidden(D_375,k2_zfmisc_1('#skF_12',B_376)) ),
    inference(resolution,[status(thm)],[c_6839,c_5310])).

tff(c_6865,plain,(
    ! [B_376] : k2_zfmisc_1('#skF_12',B_376) = '#skF_12' ),
    inference(resolution,[status(thm)],[c_5183,c_6850])).

tff(c_64,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_5261,plain,
    ( '#skF_10' = '#skF_12'
    | '#skF_9' = '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5181,c_5181,c_5181,c_64])).

tff(c_5262,plain,(
    '#skF_9' = '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_5261])).

tff(c_5180,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_5192,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5181,c_5180])).

tff(c_5263,plain,(
    k2_zfmisc_1('#skF_12','#skF_10') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5262,c_5192])).

tff(c_6869,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6865,c_5263])).

tff(c_6870,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_5261])).

tff(c_6872,plain,(
    k2_zfmisc_1('#skF_9','#skF_12') != '#skF_12' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6870,c_5192])).

tff(c_9056,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9052,c_6872])).

tff(c_9058,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_10'
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_9080,plain,
    ( '#skF_11' = '#skF_10'
    | '#skF_11' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_9058,c_9058,c_68])).

tff(c_9081,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_9080])).

tff(c_9077,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_11' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_8])).

tff(c_9084,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9081,c_9077])).

tff(c_10986,plain,(
    ! [A_534,B_535,D_536] :
      ( r2_hidden('#skF_7'(A_534,B_535,k2_zfmisc_1(A_534,B_535),D_536),A_534)
      | ~ r2_hidden(D_536,k2_zfmisc_1(A_534,B_535)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_9060,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_11') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_12])).

tff(c_9087,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9081,c_9060])).

tff(c_9216,plain,(
    ! [A_466,B_467,C_468] :
      ( ~ r1_xboole_0(A_466,B_467)
      | ~ r2_hidden(C_468,k3_xboole_0(A_466,B_467)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_9222,plain,(
    ! [A_469,B_470] :
      ( ~ r1_xboole_0(A_469,B_470)
      | k3_xboole_0(A_469,B_470) = '#skF_9' ) ),
    inference(resolution,[status(thm)],[c_9084,c_9216])).

tff(c_9227,plain,(
    ! [A_471] : k3_xboole_0(A_471,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9087,c_9222])).

tff(c_9232,plain,(
    ! [A_471,C_7] :
      ( ~ r1_xboole_0(A_471,'#skF_9')
      | ~ r2_hidden(C_7,'#skF_9') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9227,c_6])).

tff(c_9237,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_9087,c_9232])).

tff(c_11001,plain,(
    ! [D_537,B_538] : ~ r2_hidden(D_537,k2_zfmisc_1('#skF_9',B_538)) ),
    inference(resolution,[status(thm)],[c_10986,c_9237])).

tff(c_11024,plain,(
    ! [B_538] : k2_zfmisc_1('#skF_9',B_538) = '#skF_9' ),
    inference(resolution,[status(thm)],[c_9084,c_11001])).

tff(c_9057,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_9066,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9058,c_9057])).

tff(c_9086,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9081,c_9066])).

tff(c_11028,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11024,c_9086])).

tff(c_11029,plain,(
    '#skF_11' = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_9080])).

tff(c_11031,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | A_8 = '#skF_10' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11029,c_9077])).

tff(c_12550,plain,(
    ! [A_607,B_608,D_609] :
      ( r2_hidden('#skF_8'(A_607,B_608,k2_zfmisc_1(A_607,B_608),D_609),B_608)
      | ~ r2_hidden(D_609,k2_zfmisc_1(A_607,B_608)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11034,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11029,c_9060])).

tff(c_11166,plain,(
    ! [A_549,B_550,C_551] :
      ( ~ r1_xboole_0(A_549,B_550)
      | ~ r2_hidden(C_551,k3_xboole_0(A_549,B_550)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11172,plain,(
    ! [A_552,B_553] :
      ( ~ r1_xboole_0(A_552,B_553)
      | k3_xboole_0(A_552,B_553) = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_11031,c_11166])).

tff(c_11177,plain,(
    ! [A_554] : k3_xboole_0(A_554,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_11034,c_11172])).

tff(c_11182,plain,(
    ! [A_554,C_7] :
      ( ~ r1_xboole_0(A_554,'#skF_10')
      | ~ r2_hidden(C_7,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11177,c_6])).

tff(c_11187,plain,(
    ! [C_7] : ~ r2_hidden(C_7,'#skF_10') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11034,c_11182])).

tff(c_12561,plain,(
    ! [D_610,A_611] : ~ r2_hidden(D_610,k2_zfmisc_1(A_611,'#skF_10')) ),
    inference(resolution,[status(thm)],[c_12550,c_11187])).

tff(c_12576,plain,(
    ! [A_611] : k2_zfmisc_1(A_611,'#skF_10') = '#skF_10' ),
    inference(resolution,[status(thm)],[c_11031,c_12561])).

tff(c_11033,plain,(
    k2_zfmisc_1('#skF_9','#skF_10') != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11029,c_9066])).

tff(c_12580,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12576,c_11033])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:53:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.94/2.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/2.72  
% 6.94/2.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/2.72  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_11 > #skF_6 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_1 > #skF_12
% 6.94/2.72  
% 6.94/2.72  %Foreground sorts:
% 6.94/2.72  
% 6.94/2.72  
% 6.94/2.72  %Background operators:
% 6.94/2.72  
% 6.94/2.72  
% 6.94/2.72  %Foreground operators:
% 6.94/2.72  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.94/2.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.94/2.72  tff('#skF_11', type, '#skF_11': $i).
% 6.94/2.72  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 6.94/2.72  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.94/2.72  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.94/2.72  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.94/2.72  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.94/2.72  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.94/2.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.94/2.72  tff('#skF_10', type, '#skF_10': $i).
% 6.94/2.72  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 6.94/2.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.94/2.72  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.94/2.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.94/2.72  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.94/2.72  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.94/2.72  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.94/2.72  tff('#skF_9', type, '#skF_9': $i).
% 6.94/2.72  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.94/2.72  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.94/2.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.94/2.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.94/2.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.94/2.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.94/2.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.94/2.72  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.94/2.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.94/2.72  tff('#skF_12', type, '#skF_12': $i).
% 6.94/2.72  
% 6.94/2.74  tff(f_96, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.94/2.74  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.94/2.74  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 6.94/2.74  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.94/2.74  tff(f_89, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.94/2.74  tff(f_81, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.94/2.74  tff(c_62, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_171, plain, (k1_xboole_0!='#skF_12'), inference(splitLeft, [status(thm)], [c_62])).
% 6.94/2.74  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.94/2.74  tff(c_66, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_83, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_66])).
% 6.94/2.74  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.94/2.74  tff(c_197, plain, (![A_94, B_95, C_96]: (~r1_xboole_0(A_94, B_95) | ~r2_hidden(C_96, k3_xboole_0(A_94, B_95)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_203, plain, (![A_97, B_98]: (~r1_xboole_0(A_97, B_98) | k3_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_197])).
% 6.94/2.74  tff(c_208, plain, (![A_99]: (k3_xboole_0(A_99, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_203])).
% 6.94/2.74  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_213, plain, (![A_99, C_7]: (~r1_xboole_0(A_99, k1_xboole_0) | ~r2_hidden(C_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_208, c_6])).
% 6.94/2.74  tff(c_218, plain, (![C_7]: (~r2_hidden(C_7, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_213])).
% 6.94/2.74  tff(c_72, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_191, plain, (k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 6.94/2.74  tff(c_719, plain, (![A_136, B_137, C_138, D_139]: (r2_hidden(k4_tarski(A_136, B_137), k2_zfmisc_1(C_138, D_139)) | ~r2_hidden(B_137, D_139) | ~r2_hidden(A_136, C_138))), inference(cnfTransformation, [status(thm)], [f_89])).
% 6.94/2.74  tff(c_728, plain, (![A_136, B_137]: (r2_hidden(k4_tarski(A_136, B_137), k1_xboole_0) | ~r2_hidden(B_137, '#skF_12') | ~r2_hidden(A_136, '#skF_11'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_719])).
% 6.94/2.74  tff(c_731, plain, (![B_137, A_136]: (~r2_hidden(B_137, '#skF_12') | ~r2_hidden(A_136, '#skF_11'))), inference(negUnitSimplification, [status(thm)], [c_218, c_728])).
% 6.94/2.74  tff(c_733, plain, (![A_140]: (~r2_hidden(A_140, '#skF_11'))), inference(splitLeft, [status(thm)], [c_731])).
% 6.94/2.74  tff(c_737, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_8, c_733])).
% 6.94/2.74  tff(c_741, plain, $false, inference(negUnitSimplification, [status(thm)], [c_83, c_737])).
% 6.94/2.74  tff(c_743, plain, (![B_141]: (~r2_hidden(B_141, '#skF_12'))), inference(splitRight, [status(thm)], [c_731])).
% 6.94/2.74  tff(c_747, plain, (k1_xboole_0='#skF_12'), inference(resolution, [status(thm)], [c_8, c_743])).
% 6.94/2.74  tff(c_751, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_747])).
% 6.94/2.74  tff(c_752, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_72])).
% 6.94/2.74  tff(c_754, plain, (k1_xboole_0='#skF_10'), inference(splitLeft, [status(thm)], [c_752])).
% 6.94/2.74  tff(c_757, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_754, c_8])).
% 6.94/2.74  tff(c_2813, plain, (![A_217, B_218, D_219]: (r2_hidden('#skF_8'(A_217, B_218, k2_zfmisc_1(A_217, B_218), D_219), B_218) | ~r2_hidden(D_219, k2_zfmisc_1(A_217, B_218)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_760, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_754, c_12])).
% 6.94/2.74  tff(c_834, plain, (![A_146, B_147, C_148]: (~r1_xboole_0(A_146, B_147) | ~r2_hidden(C_148, k3_xboole_0(A_146, B_147)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_849, plain, (![A_152, B_153]: (~r1_xboole_0(A_152, B_153) | k3_xboole_0(A_152, B_153)='#skF_10')), inference(resolution, [status(thm)], [c_757, c_834])).
% 6.94/2.74  tff(c_854, plain, (![A_154]: (k3_xboole_0(A_154, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_760, c_849])).
% 6.94/2.74  tff(c_859, plain, (![A_154, C_7]: (~r1_xboole_0(A_154, '#skF_10') | ~r2_hidden(C_7, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_854, c_6])).
% 6.94/2.74  tff(c_864, plain, (![C_7]: (~r2_hidden(C_7, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_760, c_859])).
% 6.94/2.74  tff(c_2828, plain, (![D_220, A_221]: (~r2_hidden(D_220, k2_zfmisc_1(A_221, '#skF_10')))), inference(resolution, [status(thm)], [c_2813, c_864])).
% 6.94/2.74  tff(c_2851, plain, (![A_221]: (k2_zfmisc_1(A_221, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_757, c_2828])).
% 6.94/2.74  tff(c_70, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0 | k2_zfmisc_1('#skF_11', '#skF_12')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_789, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_754, c_754, c_70])).
% 6.94/2.74  tff(c_790, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(splitLeft, [status(thm)], [c_789])).
% 6.94/2.74  tff(c_2855, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2851, c_790])).
% 6.94/2.74  tff(c_2856, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_10'), inference(splitRight, [status(thm)], [c_789])).
% 6.94/2.74  tff(c_753, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 6.94/2.74  tff(c_2867, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2856, c_754, c_753])).
% 6.94/2.74  tff(c_2868, plain, (k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_752])).
% 6.94/2.74  tff(c_5174, plain, (k2_zfmisc_1('#skF_11', '#skF_12')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_753])).
% 6.94/2.74  tff(c_2872, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_8])).
% 6.94/2.74  tff(c_5128, plain, (![A_298, B_299, D_300]: (r2_hidden('#skF_7'(A_298, B_299, k2_zfmisc_1(A_298, B_299), D_300), A_298) | ~r2_hidden(D_300, k2_zfmisc_1(A_298, B_299)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_2875, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_12])).
% 6.94/2.74  tff(c_2949, plain, (![A_226, B_227, C_228]: (~r1_xboole_0(A_226, B_227) | ~r2_hidden(C_228, k3_xboole_0(A_226, B_227)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_2956, plain, (![A_229, B_230]: (~r1_xboole_0(A_229, B_230) | k3_xboole_0(A_229, B_230)='#skF_9')), inference(resolution, [status(thm)], [c_2872, c_2949])).
% 6.94/2.74  tff(c_2961, plain, (![A_231]: (k3_xboole_0(A_231, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_2875, c_2956])).
% 6.94/2.74  tff(c_2966, plain, (![A_231, C_7]: (~r1_xboole_0(A_231, '#skF_9') | ~r2_hidden(C_7, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_2961, c_6])).
% 6.94/2.74  tff(c_2971, plain, (![C_7]: (~r2_hidden(C_7, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_2875, c_2966])).
% 6.94/2.74  tff(c_5143, plain, (![D_301, B_302]: (~r2_hidden(D_301, k2_zfmisc_1('#skF_9', B_302)))), inference(resolution, [status(thm)], [c_5128, c_2971])).
% 6.94/2.74  tff(c_5166, plain, (![B_302]: (k2_zfmisc_1('#skF_9', B_302)='#skF_9')), inference(resolution, [status(thm)], [c_2872, c_5143])).
% 6.94/2.74  tff(c_2881, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9' | k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_2868, c_2868, c_70])).
% 6.94/2.74  tff(c_2882, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(splitLeft, [status(thm)], [c_2881])).
% 6.94/2.74  tff(c_5170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5166, c_2882])).
% 6.94/2.74  tff(c_5171, plain, (k2_zfmisc_1('#skF_11', '#skF_12')='#skF_9'), inference(splitRight, [status(thm)], [c_2881])).
% 6.94/2.74  tff(c_5179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5174, c_5171])).
% 6.94/2.74  tff(c_5181, plain, (k1_xboole_0='#skF_12'), inference(splitRight, [status(thm)], [c_62])).
% 6.94/2.74  tff(c_5183, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_12')), inference(demodulation, [status(thm), theory('equality')], [c_5181, c_8])).
% 6.94/2.74  tff(c_9026, plain, (![A_448, B_449, D_450]: (r2_hidden('#skF_8'(A_448, B_449, k2_zfmisc_1(A_448, B_449), D_450), B_449) | ~r2_hidden(D_450, k2_zfmisc_1(A_448, B_449)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_5186, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5181, c_12])).
% 6.94/2.74  tff(c_6898, plain, (![A_382, B_383, C_384]: (~r1_xboole_0(A_382, B_383) | ~r2_hidden(C_384, k3_xboole_0(A_382, B_383)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_6904, plain, (![A_385, B_386]: (~r1_xboole_0(A_385, B_386) | k3_xboole_0(A_385, B_386)='#skF_12')), inference(resolution, [status(thm)], [c_5183, c_6898])).
% 6.94/2.74  tff(c_6909, plain, (![A_387]: (k3_xboole_0(A_387, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_5186, c_6904])).
% 6.94/2.74  tff(c_6914, plain, (![A_387, C_7]: (~r1_xboole_0(A_387, '#skF_12') | ~r2_hidden(C_7, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_6909, c_6])).
% 6.94/2.74  tff(c_6919, plain, (![C_7]: (~r2_hidden(C_7, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5186, c_6914])).
% 6.94/2.74  tff(c_9037, plain, (![D_451, A_452]: (~r2_hidden(D_451, k2_zfmisc_1(A_452, '#skF_12')))), inference(resolution, [status(thm)], [c_9026, c_6919])).
% 6.94/2.74  tff(c_9052, plain, (![A_452]: (k2_zfmisc_1(A_452, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_5183, c_9037])).
% 6.94/2.74  tff(c_6839, plain, (![A_372, B_373, D_374]: (r2_hidden('#skF_7'(A_372, B_373, k2_zfmisc_1(A_372, B_373), D_374), A_372) | ~r2_hidden(D_374, k2_zfmisc_1(A_372, B_373)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_5289, plain, (![A_312, B_313, C_314]: (~r1_xboole_0(A_312, B_313) | ~r2_hidden(C_314, k3_xboole_0(A_312, B_313)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_5295, plain, (![A_315, B_316]: (~r1_xboole_0(A_315, B_316) | k3_xboole_0(A_315, B_316)='#skF_12')), inference(resolution, [status(thm)], [c_5183, c_5289])).
% 6.94/2.74  tff(c_5300, plain, (![A_317]: (k3_xboole_0(A_317, '#skF_12')='#skF_12')), inference(resolution, [status(thm)], [c_5186, c_5295])).
% 6.94/2.74  tff(c_5305, plain, (![A_317, C_7]: (~r1_xboole_0(A_317, '#skF_12') | ~r2_hidden(C_7, '#skF_12'))), inference(superposition, [status(thm), theory('equality')], [c_5300, c_6])).
% 6.94/2.74  tff(c_5310, plain, (![C_7]: (~r2_hidden(C_7, '#skF_12'))), inference(demodulation, [status(thm), theory('equality')], [c_5186, c_5305])).
% 6.94/2.74  tff(c_6850, plain, (![D_375, B_376]: (~r2_hidden(D_375, k2_zfmisc_1('#skF_12', B_376)))), inference(resolution, [status(thm)], [c_6839, c_5310])).
% 6.94/2.74  tff(c_6865, plain, (![B_376]: (k2_zfmisc_1('#skF_12', B_376)='#skF_12')), inference(resolution, [status(thm)], [c_5183, c_6850])).
% 6.94/2.74  tff(c_64, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_5261, plain, ('#skF_10'='#skF_12' | '#skF_9'='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5181, c_5181, c_5181, c_64])).
% 6.94/2.74  tff(c_5262, plain, ('#skF_9'='#skF_12'), inference(splitLeft, [status(thm)], [c_5261])).
% 6.94/2.74  tff(c_5180, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_62])).
% 6.94/2.74  tff(c_5192, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5181, c_5180])).
% 6.94/2.74  tff(c_5263, plain, (k2_zfmisc_1('#skF_12', '#skF_10')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_5262, c_5192])).
% 6.94/2.74  tff(c_6869, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6865, c_5263])).
% 6.94/2.74  tff(c_6870, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_5261])).
% 6.94/2.74  tff(c_6872, plain, (k2_zfmisc_1('#skF_9', '#skF_12')!='#skF_12'), inference(demodulation, [status(thm), theory('equality')], [c_6870, c_5192])).
% 6.94/2.74  tff(c_9056, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9052, c_6872])).
% 6.94/2.74  tff(c_9058, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_66])).
% 6.94/2.74  tff(c_68, plain, (k1_xboole_0='#skF_10' | k1_xboole_0='#skF_9' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.94/2.74  tff(c_9080, plain, ('#skF_11'='#skF_10' | '#skF_11'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_9058, c_9058, c_68])).
% 6.94/2.74  tff(c_9081, plain, ('#skF_11'='#skF_9'), inference(splitLeft, [status(thm)], [c_9080])).
% 6.94/2.74  tff(c_9077, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_8])).
% 6.94/2.74  tff(c_9084, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_9081, c_9077])).
% 6.94/2.74  tff(c_10986, plain, (![A_534, B_535, D_536]: (r2_hidden('#skF_7'(A_534, B_535, k2_zfmisc_1(A_534, B_535), D_536), A_534) | ~r2_hidden(D_536, k2_zfmisc_1(A_534, B_535)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_9060, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_11'))), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_12])).
% 6.94/2.74  tff(c_9087, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9081, c_9060])).
% 6.94/2.74  tff(c_9216, plain, (![A_466, B_467, C_468]: (~r1_xboole_0(A_466, B_467) | ~r2_hidden(C_468, k3_xboole_0(A_466, B_467)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_9222, plain, (![A_469, B_470]: (~r1_xboole_0(A_469, B_470) | k3_xboole_0(A_469, B_470)='#skF_9')), inference(resolution, [status(thm)], [c_9084, c_9216])).
% 6.94/2.74  tff(c_9227, plain, (![A_471]: (k3_xboole_0(A_471, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_9087, c_9222])).
% 6.94/2.74  tff(c_9232, plain, (![A_471, C_7]: (~r1_xboole_0(A_471, '#skF_9') | ~r2_hidden(C_7, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_9227, c_6])).
% 6.94/2.74  tff(c_9237, plain, (![C_7]: (~r2_hidden(C_7, '#skF_9'))), inference(demodulation, [status(thm), theory('equality')], [c_9087, c_9232])).
% 6.94/2.74  tff(c_11001, plain, (![D_537, B_538]: (~r2_hidden(D_537, k2_zfmisc_1('#skF_9', B_538)))), inference(resolution, [status(thm)], [c_10986, c_9237])).
% 6.94/2.74  tff(c_11024, plain, (![B_538]: (k2_zfmisc_1('#skF_9', B_538)='#skF_9')), inference(resolution, [status(thm)], [c_9084, c_11001])).
% 6.94/2.74  tff(c_9057, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_66])).
% 6.94/2.74  tff(c_9066, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_9058, c_9057])).
% 6.94/2.74  tff(c_9086, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_9081, c_9066])).
% 6.94/2.74  tff(c_11028, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11024, c_9086])).
% 6.94/2.74  tff(c_11029, plain, ('#skF_11'='#skF_10'), inference(splitRight, [status(thm)], [c_9080])).
% 6.94/2.74  tff(c_11031, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | A_8='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_11029, c_9077])).
% 6.94/2.74  tff(c_12550, plain, (![A_607, B_608, D_609]: (r2_hidden('#skF_8'(A_607, B_608, k2_zfmisc_1(A_607, B_608), D_609), B_608) | ~r2_hidden(D_609, k2_zfmisc_1(A_607, B_608)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.94/2.74  tff(c_11034, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11029, c_9060])).
% 6.94/2.74  tff(c_11166, plain, (![A_549, B_550, C_551]: (~r1_xboole_0(A_549, B_550) | ~r2_hidden(C_551, k3_xboole_0(A_549, B_550)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.94/2.74  tff(c_11172, plain, (![A_552, B_553]: (~r1_xboole_0(A_552, B_553) | k3_xboole_0(A_552, B_553)='#skF_10')), inference(resolution, [status(thm)], [c_11031, c_11166])).
% 6.94/2.74  tff(c_11177, plain, (![A_554]: (k3_xboole_0(A_554, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_11034, c_11172])).
% 6.94/2.74  tff(c_11182, plain, (![A_554, C_7]: (~r1_xboole_0(A_554, '#skF_10') | ~r2_hidden(C_7, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_11177, c_6])).
% 6.94/2.74  tff(c_11187, plain, (![C_7]: (~r2_hidden(C_7, '#skF_10'))), inference(demodulation, [status(thm), theory('equality')], [c_11034, c_11182])).
% 6.94/2.74  tff(c_12561, plain, (![D_610, A_611]: (~r2_hidden(D_610, k2_zfmisc_1(A_611, '#skF_10')))), inference(resolution, [status(thm)], [c_12550, c_11187])).
% 6.94/2.74  tff(c_12576, plain, (![A_611]: (k2_zfmisc_1(A_611, '#skF_10')='#skF_10')), inference(resolution, [status(thm)], [c_11031, c_12561])).
% 6.94/2.74  tff(c_11033, plain, (k2_zfmisc_1('#skF_9', '#skF_10')!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_11029, c_9066])).
% 6.94/2.74  tff(c_12580, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12576, c_11033])).
% 6.94/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.94/2.74  
% 6.94/2.74  Inference rules
% 6.94/2.74  ----------------------
% 6.94/2.74  #Ref     : 0
% 6.94/2.74  #Sup     : 3086
% 6.94/2.74  #Fact    : 0
% 6.94/2.74  #Define  : 0
% 6.94/2.74  #Split   : 12
% 6.94/2.74  #Chain   : 0
% 6.94/2.74  #Close   : 0
% 6.94/2.74  
% 6.94/2.74  Ordering : KBO
% 6.94/2.74  
% 6.94/2.74  Simplification rules
% 6.94/2.74  ----------------------
% 6.94/2.74  #Subsume      : 206
% 6.94/2.74  #Demod        : 2151
% 6.94/2.74  #Tautology    : 1592
% 6.94/2.74  #SimpNegUnit  : 22
% 6.94/2.74  #BackRed      : 46
% 6.94/2.74  
% 6.94/2.74  #Partial instantiations: 0
% 6.94/2.74  #Strategies tried      : 1
% 6.94/2.74  
% 6.94/2.74  Timing (in seconds)
% 6.94/2.74  ----------------------
% 6.94/2.75  Preprocessing        : 0.34
% 6.94/2.75  Parsing              : 0.17
% 6.94/2.75  CNF conversion       : 0.03
% 6.94/2.75  Main loop            : 1.59
% 6.94/2.75  Inferencing          : 0.48
% 6.94/2.75  Reduction            : 0.75
% 6.94/2.75  Demodulation         : 0.63
% 6.94/2.75  BG Simplification    : 0.08
% 6.94/2.75  Subsumption          : 0.19
% 6.94/2.75  Abstraction          : 0.09
% 6.94/2.75  MUC search           : 0.00
% 6.94/2.75  Cooper               : 0.00
% 6.94/2.75  Total                : 1.98
% 6.94/2.75  Index Insertion      : 0.00
% 6.94/2.75  Index Deletion       : 0.00
% 6.94/2.75  Index Matching       : 0.00
% 6.94/2.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
