%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:43 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.18s
% Verified   : 
% Statistics : Number of formulae       :  166 ( 563 expanded)
%              Number of leaves         :   42 ( 182 expanded)
%              Depth                    :   10
%              Number of atoms          :  177 (1025 expanded)
%              Number of equality atoms :  114 ( 900 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_111,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_zfmisc_1(A,B) = k1_xboole_0
      <=> ( A = k1_xboole_0
          | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_104,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(c_78,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_129,plain,(
    k1_xboole_0 != '#skF_11' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_6,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_84,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_130,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_192,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k3_xboole_0(A_113,B_114)) = k4_xboole_0(A_113,B_114) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_201,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_192])).

tff(c_205,plain,(
    ! [A_115] : k4_xboole_0(A_115,A_115) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_201])).

tff(c_74,plain,(
    ! [C_92,B_91] : ~ r2_hidden(C_92,k4_xboole_0(B_91,k1_tarski(C_92))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_210,plain,(
    ! [C_92] : ~ r2_hidden(C_92,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_74])).

tff(c_88,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_169,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_1180,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( r2_hidden(k4_tarski(A_171,B_172),k2_zfmisc_1(C_173,D_174))
      | ~ r2_hidden(B_172,D_174)
      | ~ r2_hidden(A_171,C_173) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1189,plain,(
    ! [A_171,B_172] :
      ( r2_hidden(k4_tarski(A_171,B_172),k1_xboole_0)
      | ~ r2_hidden(B_172,'#skF_11')
      | ~ r2_hidden(A_171,'#skF_10') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_1180])).

tff(c_1192,plain,(
    ! [B_172,A_171] :
      ( ~ r2_hidden(B_172,'#skF_11')
      | ~ r2_hidden(A_171,'#skF_10') ) ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_1189])).

tff(c_1194,plain,(
    ! [A_175] : ~ r2_hidden(A_175,'#skF_10') ),
    inference(splitLeft,[status(thm)],[c_1192])).

tff(c_1198,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(resolution,[status(thm)],[c_6,c_1194])).

tff(c_1202,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_130,c_1198])).

tff(c_1204,plain,(
    ! [B_176] : ~ r2_hidden(B_176,'#skF_11') ),
    inference(splitRight,[status(thm)],[c_1192])).

tff(c_1208,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(resolution,[status(thm)],[c_6,c_1204])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_1208])).

tff(c_1213,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1215,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1213])).

tff(c_1217,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_6])).

tff(c_2397,plain,(
    ! [A_254,B_255,D_256] :
      ( r2_hidden('#skF_7'(A_254,B_255,k2_zfmisc_1(A_254,B_255),D_256),B_255)
      | ~ r2_hidden(D_256,k2_zfmisc_1(A_254,B_255)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1220,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_16])).

tff(c_1258,plain,(
    ! [A_181,B_182] : k5_xboole_0(A_181,k3_xboole_0(A_181,B_182)) = k4_xboole_0(A_181,B_182) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1267,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1258])).

tff(c_1271,plain,(
    ! [A_183] : k4_xboole_0(A_183,A_183) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1220,c_1267])).

tff(c_1276,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_1271,c_74])).

tff(c_2423,plain,(
    ! [D_257,A_258] : ~ r2_hidden(D_257,k2_zfmisc_1(A_258,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_2397,c_1276])).

tff(c_2438,plain,(
    ! [A_258] : k2_zfmisc_1(A_258,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1217,c_2423])).

tff(c_86,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k2_zfmisc_1('#skF_10','#skF_11') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1235,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_1215,c_86])).

tff(c_1236,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_1235])).

tff(c_2442,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2438,c_1236])).

tff(c_2443,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1235])).

tff(c_1214,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_2461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2443,c_1215,c_1214])).

tff(c_2462,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_1213])).

tff(c_3988,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2462,c_1214])).

tff(c_2465,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2462,c_6])).

tff(c_3928,plain,(
    ! [A_349,B_350,D_351] :
      ( r2_hidden('#skF_6'(A_349,B_350,k2_zfmisc_1(A_349,B_350),D_351),A_349)
      | ~ r2_hidden(D_351,k2_zfmisc_1(A_349,B_350)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2468,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2462,c_16])).

tff(c_2514,plain,(
    ! [A_265,B_266] : k5_xboole_0(A_265,k3_xboole_0(A_265,B_266)) = k4_xboole_0(A_265,B_266) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2523,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_2514])).

tff(c_2527,plain,(
    ! [A_267] : k4_xboole_0(A_267,A_267) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2468,c_2523])).

tff(c_2532,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2527,c_74])).

tff(c_3958,plain,(
    ! [D_352,B_353] : ~ r2_hidden(D_352,k2_zfmisc_1('#skF_8',B_353)) ),
    inference(resolution,[status(thm)],[c_3928,c_2532])).

tff(c_3981,plain,(
    ! [B_353] : k2_zfmisc_1('#skF_8',B_353) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_2465,c_3958])).

tff(c_2476,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8'
    | k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2462,c_2462,c_86])).

tff(c_2477,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_2476])).

tff(c_3985,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3981,c_2477])).

tff(c_3986,plain,(
    k2_zfmisc_1('#skF_10','#skF_11') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_2476])).

tff(c_3997,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3988,c_3986])).

tff(c_3999,plain,(
    k1_xboole_0 = '#skF_10' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_3998,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4020,plain,
    ( '#skF_10' = '#skF_8'
    | '#skF_10' = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3999,c_3999,c_3998])).

tff(c_4021,plain,(
    '#skF_10' = '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_4020])).

tff(c_4027,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4021,c_3999])).

tff(c_4051,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4027,c_6])).

tff(c_5309,plain,(
    ! [A_450,B_451,D_452] :
      ( r2_hidden('#skF_7'(A_450,B_451,k2_zfmisc_1(A_450,B_451),D_452),B_451)
      | ~ r2_hidden(D_452,k2_zfmisc_1(A_450,B_451)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_4001,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3999,c_16])).

tff(c_4023,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4021,c_4001])).

tff(c_4102,plain,(
    ! [A_370,B_371] : k5_xboole_0(A_370,k3_xboole_0(A_370,B_371)) = k4_xboole_0(A_370,B_371) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4111,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_4102])).

tff(c_4115,plain,(
    ! [A_372] : k4_xboole_0(A_372,A_372) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4023,c_4111])).

tff(c_4120,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_4115,c_74])).

tff(c_5339,plain,(
    ! [D_453,A_454] : ~ r2_hidden(D_453,k2_zfmisc_1(A_454,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_5309,c_4120])).

tff(c_5362,plain,(
    ! [A_454] : k2_zfmisc_1(A_454,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_4051,c_5339])).

tff(c_82,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_10' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4050,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4027,c_4021,c_4027,c_82])).

tff(c_5366,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5362,c_4050])).

tff(c_5367,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4020])).

tff(c_5373,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_3999])).

tff(c_5411,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_6])).

tff(c_6918,plain,(
    ! [A_550,B_551,D_552] :
      ( r2_hidden('#skF_6'(A_550,B_551,k2_zfmisc_1(A_550,B_551),D_552),A_550)
      | ~ r2_hidden(D_552,k2_zfmisc_1(A_550,B_551)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_5369,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_4001])).

tff(c_5475,plain,(
    ! [A_473,B_474] : k5_xboole_0(A_473,k3_xboole_0(A_473,B_474)) = k4_xboole_0(A_473,B_474) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_5484,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_5475])).

tff(c_5489,plain,(
    ! [A_475] : k4_xboole_0(A_475,A_475) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5369,c_5484])).

tff(c_5494,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_5489,c_74])).

tff(c_6948,plain,(
    ! [D_553,B_554] : ~ r2_hidden(D_553,k2_zfmisc_1('#skF_8',B_554)) ),
    inference(resolution,[status(thm)],[c_6918,c_5494])).

tff(c_6971,plain,(
    ! [B_554] : k2_zfmisc_1('#skF_8',B_554) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5411,c_6948])).

tff(c_5378,plain,
    ( k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0
    | k1_xboole_0 != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5367,c_82])).

tff(c_5379,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5378])).

tff(c_5386,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_5379])).

tff(c_5387,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_5378])).

tff(c_5402,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_5387])).

tff(c_6975,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6971,c_5402])).

tff(c_6977,plain,(
    k1_xboole_0 = '#skF_11' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_80,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 != '#skF_11' ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_7001,plain,
    ( '#skF_11' = '#skF_9'
    | '#skF_11' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_6977,c_6977,c_80])).

tff(c_7002,plain,(
    '#skF_11' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_7001])).

tff(c_7008,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7002,c_6977])).

tff(c_7030,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_8' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7008,c_6])).

tff(c_8404,plain,(
    ! [A_652,B_653,D_654] :
      ( r2_hidden('#skF_6'(A_652,B_653,k2_zfmisc_1(A_652,B_653),D_654),A_652)
      | ~ r2_hidden(D_654,k2_zfmisc_1(A_652,B_653)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6978,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_16])).

tff(c_7003,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7002,c_6978])).

tff(c_7088,plain,(
    ! [A_572,B_573] : k5_xboole_0(A_572,k3_xboole_0(A_572,B_573)) = k4_xboole_0(A_572,B_573) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7097,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_7088])).

tff(c_7101,plain,(
    ! [A_574] : k4_xboole_0(A_574,A_574) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7003,c_7097])).

tff(c_7106,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_7101,c_74])).

tff(c_8434,plain,(
    ! [D_655,B_656] : ~ r2_hidden(D_655,k2_zfmisc_1('#skF_8',B_656)) ),
    inference(resolution,[status(thm)],[c_8404,c_7106])).

tff(c_8457,plain,(
    ! [B_656] : k2_zfmisc_1('#skF_8',B_656) = '#skF_8' ),
    inference(resolution,[status(thm)],[c_7030,c_8434])).

tff(c_6976,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6992,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_11' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6977,c_6976])).

tff(c_7004,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7002,c_6992])).

tff(c_8461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8457,c_7004])).

tff(c_8462,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_7001])).

tff(c_8469,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8462,c_6977])).

tff(c_8495,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_1'(A_5),A_5)
      | A_5 = '#skF_9' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8469,c_6])).

tff(c_9857,plain,(
    ! [A_752,B_753,D_754] :
      ( r2_hidden('#skF_7'(A_752,B_753,k2_zfmisc_1(A_752,B_753),D_754),B_753)
      | ~ r2_hidden(D_754,k2_zfmisc_1(A_752,B_753)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8464,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8462,c_6978])).

tff(c_8538,plain,(
    ! [A_669,B_670] : k5_xboole_0(A_669,k3_xboole_0(A_669,B_670)) = k4_xboole_0(A_669,B_670) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8547,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_8538])).

tff(c_8551,plain,(
    ! [A_671] : k4_xboole_0(A_671,A_671) = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8464,c_8547])).

tff(c_8556,plain,(
    ! [C_92] : ~ r2_hidden(C_92,'#skF_9') ),
    inference(superposition,[status(thm),theory(equality)],[c_8551,c_74])).

tff(c_9887,plain,(
    ! [D_755,A_756] : ~ r2_hidden(D_755,k2_zfmisc_1(A_756,'#skF_9')) ),
    inference(resolution,[status(thm)],[c_9857,c_8556])).

tff(c_9910,plain,(
    ! [A_756] : k2_zfmisc_1(A_756,'#skF_9') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_8495,c_9887])).

tff(c_8465,plain,(
    k2_zfmisc_1('#skF_8','#skF_9') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8462,c_6992])).

tff(c_9914,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9910,c_8465])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:28:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.31  
% 6.18/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_11 > #skF_1 > #skF_4 > #skF_10 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_9 > #skF_8 > #skF_3
% 6.18/2.31  
% 6.18/2.31  %Foreground sorts:
% 6.18/2.31  
% 6.18/2.31  
% 6.18/2.31  %Background operators:
% 6.18/2.31  
% 6.18/2.31  
% 6.18/2.31  %Foreground operators:
% 6.18/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.18/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.18/2.31  tff('#skF_11', type, '#skF_11': $i).
% 6.18/2.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.18/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.18/2.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.18/2.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 6.18/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.18/2.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.18/2.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.18/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.18/2.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_10', type, '#skF_10': $i).
% 6.18/2.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.18/2.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 6.18/2.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.18/2.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.18/2.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 6.18/2.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_9', type, '#skF_9': $i).
% 6.18/2.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.18/2.31  tff('#skF_8', type, '#skF_8': $i).
% 6.18/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.18/2.31  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.18/2.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.18/2.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.18/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.18/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.18/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.18/2.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.18/2.31  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.18/2.31  
% 6.18/2.33  tff(f_111, negated_conjecture, ~(![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.18/2.33  tff(f_37, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.18/2.33  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.18/2.33  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 6.18/2.33  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.18/2.33  tff(f_104, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 6.18/2.33  tff(f_96, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 6.18/2.33  tff(f_81, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 6.18/2.33  tff(c_78, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_129, plain, (k1_xboole_0!='#skF_11'), inference(splitLeft, [status(thm)], [c_78])).
% 6.18/2.33  tff(c_6, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.18/2.33  tff(c_84, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_130, plain, (k1_xboole_0!='#skF_10'), inference(splitLeft, [status(thm)], [c_84])).
% 6.18/2.33  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.18/2.33  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.18/2.33  tff(c_192, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k3_xboole_0(A_113, B_114))=k4_xboole_0(A_113, B_114))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_201, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_192])).
% 6.18/2.33  tff(c_205, plain, (![A_115]: (k4_xboole_0(A_115, A_115)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_201])).
% 6.18/2.33  tff(c_74, plain, (![C_92, B_91]: (~r2_hidden(C_92, k4_xboole_0(B_91, k1_tarski(C_92))))), inference(cnfTransformation, [status(thm)], [f_104])).
% 6.18/2.33  tff(c_210, plain, (![C_92]: (~r2_hidden(C_92, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_205, c_74])).
% 6.18/2.33  tff(c_88, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_169, plain, (k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_88])).
% 6.18/2.33  tff(c_1180, plain, (![A_171, B_172, C_173, D_174]: (r2_hidden(k4_tarski(A_171, B_172), k2_zfmisc_1(C_173, D_174)) | ~r2_hidden(B_172, D_174) | ~r2_hidden(A_171, C_173))), inference(cnfTransformation, [status(thm)], [f_96])).
% 6.18/2.33  tff(c_1189, plain, (![A_171, B_172]: (r2_hidden(k4_tarski(A_171, B_172), k1_xboole_0) | ~r2_hidden(B_172, '#skF_11') | ~r2_hidden(A_171, '#skF_10'))), inference(superposition, [status(thm), theory('equality')], [c_169, c_1180])).
% 6.18/2.33  tff(c_1192, plain, (![B_172, A_171]: (~r2_hidden(B_172, '#skF_11') | ~r2_hidden(A_171, '#skF_10'))), inference(negUnitSimplification, [status(thm)], [c_210, c_1189])).
% 6.18/2.33  tff(c_1194, plain, (![A_175]: (~r2_hidden(A_175, '#skF_10'))), inference(splitLeft, [status(thm)], [c_1192])).
% 6.18/2.33  tff(c_1198, plain, (k1_xboole_0='#skF_10'), inference(resolution, [status(thm)], [c_6, c_1194])).
% 6.18/2.33  tff(c_1202, plain, $false, inference(negUnitSimplification, [status(thm)], [c_130, c_1198])).
% 6.18/2.33  tff(c_1204, plain, (![B_176]: (~r2_hidden(B_176, '#skF_11'))), inference(splitRight, [status(thm)], [c_1192])).
% 6.18/2.33  tff(c_1208, plain, (k1_xboole_0='#skF_11'), inference(resolution, [status(thm)], [c_6, c_1204])).
% 6.18/2.33  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_129, c_1208])).
% 6.18/2.33  tff(c_1213, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_88])).
% 6.18/2.33  tff(c_1215, plain, (k1_xboole_0='#skF_9'), inference(splitLeft, [status(thm)], [c_1213])).
% 6.18/2.33  tff(c_1217, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_6])).
% 6.18/2.33  tff(c_2397, plain, (![A_254, B_255, D_256]: (r2_hidden('#skF_7'(A_254, B_255, k2_zfmisc_1(A_254, B_255), D_256), B_255) | ~r2_hidden(D_256, k2_zfmisc_1(A_254, B_255)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_1220, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_16])).
% 6.18/2.33  tff(c_1258, plain, (![A_181, B_182]: (k5_xboole_0(A_181, k3_xboole_0(A_181, B_182))=k4_xboole_0(A_181, B_182))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_1267, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1258])).
% 6.18/2.33  tff(c_1271, plain, (![A_183]: (k4_xboole_0(A_183, A_183)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_1220, c_1267])).
% 6.18/2.33  tff(c_1276, plain, (![C_92]: (~r2_hidden(C_92, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_1271, c_74])).
% 6.18/2.33  tff(c_2423, plain, (![D_257, A_258]: (~r2_hidden(D_257, k2_zfmisc_1(A_258, '#skF_9')))), inference(resolution, [status(thm)], [c_2397, c_1276])).
% 6.18/2.33  tff(c_2438, plain, (![A_258]: (k2_zfmisc_1(A_258, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_1217, c_2423])).
% 6.18/2.33  tff(c_86, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k2_zfmisc_1('#skF_10', '#skF_11')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_1235, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_1215, c_86])).
% 6.18/2.33  tff(c_1236, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(splitLeft, [status(thm)], [c_1235])).
% 6.18/2.33  tff(c_2442, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2438, c_1236])).
% 6.18/2.33  tff(c_2443, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_9'), inference(splitRight, [status(thm)], [c_1235])).
% 6.18/2.33  tff(c_1214, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_88])).
% 6.18/2.33  tff(c_2461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2443, c_1215, c_1214])).
% 6.18/2.33  tff(c_2462, plain, (k1_xboole_0='#skF_8'), inference(splitRight, [status(thm)], [c_1213])).
% 6.18/2.33  tff(c_3988, plain, (k2_zfmisc_1('#skF_10', '#skF_11')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2462, c_1214])).
% 6.18/2.33  tff(c_2465, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2462, c_6])).
% 6.18/2.33  tff(c_3928, plain, (![A_349, B_350, D_351]: (r2_hidden('#skF_6'(A_349, B_350, k2_zfmisc_1(A_349, B_350), D_351), A_349) | ~r2_hidden(D_351, k2_zfmisc_1(A_349, B_350)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_2468, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2462, c_16])).
% 6.18/2.33  tff(c_2514, plain, (![A_265, B_266]: (k5_xboole_0(A_265, k3_xboole_0(A_265, B_266))=k4_xboole_0(A_265, B_266))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_2523, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_2514])).
% 6.18/2.33  tff(c_2527, plain, (![A_267]: (k4_xboole_0(A_267, A_267)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2468, c_2523])).
% 6.18/2.33  tff(c_2532, plain, (![C_92]: (~r2_hidden(C_92, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_2527, c_74])).
% 6.18/2.33  tff(c_3958, plain, (![D_352, B_353]: (~r2_hidden(D_352, k2_zfmisc_1('#skF_8', B_353)))), inference(resolution, [status(thm)], [c_3928, c_2532])).
% 6.18/2.33  tff(c_3981, plain, (![B_353]: (k2_zfmisc_1('#skF_8', B_353)='#skF_8')), inference(resolution, [status(thm)], [c_2465, c_3958])).
% 6.18/2.33  tff(c_2476, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8' | k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_2462, c_2462, c_86])).
% 6.18/2.33  tff(c_2477, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(splitLeft, [status(thm)], [c_2476])).
% 6.18/2.33  tff(c_3985, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3981, c_2477])).
% 6.18/2.33  tff(c_3986, plain, (k2_zfmisc_1('#skF_10', '#skF_11')='#skF_8'), inference(splitRight, [status(thm)], [c_2476])).
% 6.18/2.33  tff(c_3997, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3988, c_3986])).
% 6.18/2.33  tff(c_3999, plain, (k1_xboole_0='#skF_10'), inference(splitRight, [status(thm)], [c_84])).
% 6.18/2.33  tff(c_3998, plain, (k1_xboole_0='#skF_8' | k1_xboole_0='#skF_9'), inference(splitRight, [status(thm)], [c_84])).
% 6.18/2.33  tff(c_4020, plain, ('#skF_10'='#skF_8' | '#skF_10'='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_3999, c_3999, c_3998])).
% 6.18/2.33  tff(c_4021, plain, ('#skF_10'='#skF_9'), inference(splitLeft, [status(thm)], [c_4020])).
% 6.18/2.33  tff(c_4027, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4021, c_3999])).
% 6.18/2.33  tff(c_4051, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4027, c_6])).
% 6.18/2.33  tff(c_5309, plain, (![A_450, B_451, D_452]: (r2_hidden('#skF_7'(A_450, B_451, k2_zfmisc_1(A_450, B_451), D_452), B_451) | ~r2_hidden(D_452, k2_zfmisc_1(A_450, B_451)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_4001, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_10')), inference(demodulation, [status(thm), theory('equality')], [c_3999, c_16])).
% 6.18/2.33  tff(c_4023, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4021, c_4001])).
% 6.18/2.33  tff(c_4102, plain, (![A_370, B_371]: (k5_xboole_0(A_370, k3_xboole_0(A_370, B_371))=k4_xboole_0(A_370, B_371))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_4111, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_4102])).
% 6.18/2.33  tff(c_4115, plain, (![A_372]: (k4_xboole_0(A_372, A_372)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_4023, c_4111])).
% 6.18/2.33  tff(c_4120, plain, (![C_92]: (~r2_hidden(C_92, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_4115, c_74])).
% 6.18/2.33  tff(c_5339, plain, (![D_453, A_454]: (~r2_hidden(D_453, k2_zfmisc_1(A_454, '#skF_9')))), inference(resolution, [status(thm)], [c_5309, c_4120])).
% 6.18/2.33  tff(c_5362, plain, (![A_454]: (k2_zfmisc_1(A_454, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_4051, c_5339])).
% 6.18/2.33  tff(c_82, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_10'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_4050, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_4027, c_4021, c_4027, c_82])).
% 6.18/2.33  tff(c_5366, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5362, c_4050])).
% 6.18/2.33  tff(c_5367, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_4020])).
% 6.18/2.33  tff(c_5373, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_3999])).
% 6.18/2.33  tff(c_5411, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_6])).
% 6.18/2.33  tff(c_6918, plain, (![A_550, B_551, D_552]: (r2_hidden('#skF_6'(A_550, B_551, k2_zfmisc_1(A_550, B_551), D_552), A_550) | ~r2_hidden(D_552, k2_zfmisc_1(A_550, B_551)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_5369, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_4001])).
% 6.18/2.33  tff(c_5475, plain, (![A_473, B_474]: (k5_xboole_0(A_473, k3_xboole_0(A_473, B_474))=k4_xboole_0(A_473, B_474))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_5484, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_5475])).
% 6.18/2.33  tff(c_5489, plain, (![A_475]: (k4_xboole_0(A_475, A_475)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_5369, c_5484])).
% 6.18/2.33  tff(c_5494, plain, (![C_92]: (~r2_hidden(C_92, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_5489, c_74])).
% 6.18/2.33  tff(c_6948, plain, (![D_553, B_554]: (~r2_hidden(D_553, k2_zfmisc_1('#skF_8', B_554)))), inference(resolution, [status(thm)], [c_6918, c_5494])).
% 6.18/2.33  tff(c_6971, plain, (![B_554]: (k2_zfmisc_1('#skF_8', B_554)='#skF_8')), inference(resolution, [status(thm)], [c_5411, c_6948])).
% 6.18/2.33  tff(c_5378, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0 | k1_xboole_0!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5367, c_82])).
% 6.18/2.33  tff(c_5379, plain, (k1_xboole_0!='#skF_8'), inference(splitLeft, [status(thm)], [c_5378])).
% 6.18/2.33  tff(c_5386, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5373, c_5379])).
% 6.18/2.33  tff(c_5387, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_5378])).
% 6.18/2.33  tff(c_5402, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_5387])).
% 6.18/2.33  tff(c_6975, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6971, c_5402])).
% 6.18/2.33  tff(c_6977, plain, (k1_xboole_0='#skF_11'), inference(splitRight, [status(thm)], [c_78])).
% 6.18/2.33  tff(c_80, plain, (k1_xboole_0='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0!='#skF_11'), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.18/2.33  tff(c_7001, plain, ('#skF_11'='#skF_9' | '#skF_11'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_6977, c_6977, c_80])).
% 6.18/2.33  tff(c_7002, plain, ('#skF_11'='#skF_8'), inference(splitLeft, [status(thm)], [c_7001])).
% 6.18/2.33  tff(c_7008, plain, (k1_xboole_0='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7002, c_6977])).
% 6.18/2.33  tff(c_7030, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7008, c_6])).
% 6.18/2.33  tff(c_8404, plain, (![A_652, B_653, D_654]: (r2_hidden('#skF_6'(A_652, B_653, k2_zfmisc_1(A_652, B_653), D_654), A_652) | ~r2_hidden(D_654, k2_zfmisc_1(A_652, B_653)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_6978, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_11')), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_16])).
% 6.18/2.33  tff(c_7003, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7002, c_6978])).
% 6.18/2.33  tff(c_7088, plain, (![A_572, B_573]: (k5_xboole_0(A_572, k3_xboole_0(A_572, B_573))=k4_xboole_0(A_572, B_573))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_7097, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_7088])).
% 6.18/2.33  tff(c_7101, plain, (![A_574]: (k4_xboole_0(A_574, A_574)='#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7003, c_7097])).
% 6.18/2.33  tff(c_7106, plain, (![C_92]: (~r2_hidden(C_92, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_7101, c_74])).
% 6.18/2.33  tff(c_8434, plain, (![D_655, B_656]: (~r2_hidden(D_655, k2_zfmisc_1('#skF_8', B_656)))), inference(resolution, [status(thm)], [c_8404, c_7106])).
% 6.18/2.33  tff(c_8457, plain, (![B_656]: (k2_zfmisc_1('#skF_8', B_656)='#skF_8')), inference(resolution, [status(thm)], [c_7030, c_8434])).
% 6.18/2.33  tff(c_6976, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_78])).
% 6.18/2.33  tff(c_6992, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_11'), inference(demodulation, [status(thm), theory('equality')], [c_6977, c_6976])).
% 6.18/2.33  tff(c_7004, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_7002, c_6992])).
% 6.18/2.33  tff(c_8461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8457, c_7004])).
% 6.18/2.33  tff(c_8462, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_7001])).
% 6.18/2.33  tff(c_8469, plain, (k1_xboole_0='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8462, c_6977])).
% 6.18/2.33  tff(c_8495, plain, (![A_5]: (r2_hidden('#skF_1'(A_5), A_5) | A_5='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8469, c_6])).
% 6.18/2.33  tff(c_9857, plain, (![A_752, B_753, D_754]: (r2_hidden('#skF_7'(A_752, B_753, k2_zfmisc_1(A_752, B_753), D_754), B_753) | ~r2_hidden(D_754, k2_zfmisc_1(A_752, B_753)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.18/2.33  tff(c_8464, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8462, c_6978])).
% 6.18/2.33  tff(c_8538, plain, (![A_669, B_670]: (k5_xboole_0(A_669, k3_xboole_0(A_669, B_670))=k4_xboole_0(A_669, B_670))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.18/2.33  tff(c_8547, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_8538])).
% 6.18/2.33  tff(c_8551, plain, (![A_671]: (k4_xboole_0(A_671, A_671)='#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8464, c_8547])).
% 6.18/2.33  tff(c_8556, plain, (![C_92]: (~r2_hidden(C_92, '#skF_9'))), inference(superposition, [status(thm), theory('equality')], [c_8551, c_74])).
% 6.18/2.33  tff(c_9887, plain, (![D_755, A_756]: (~r2_hidden(D_755, k2_zfmisc_1(A_756, '#skF_9')))), inference(resolution, [status(thm)], [c_9857, c_8556])).
% 6.18/2.33  tff(c_9910, plain, (![A_756]: (k2_zfmisc_1(A_756, '#skF_9')='#skF_9')), inference(resolution, [status(thm)], [c_8495, c_9887])).
% 6.18/2.33  tff(c_8465, plain, (k2_zfmisc_1('#skF_8', '#skF_9')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_8462, c_6992])).
% 6.18/2.33  tff(c_9914, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9910, c_8465])).
% 6.18/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.33  
% 6.18/2.33  Inference rules
% 6.18/2.33  ----------------------
% 6.18/2.33  #Ref     : 0
% 6.18/2.33  #Sup     : 2362
% 6.18/2.33  #Fact    : 0
% 6.18/2.33  #Define  : 0
% 6.18/2.33  #Split   : 19
% 6.18/2.33  #Chain   : 0
% 6.18/2.33  #Close   : 0
% 6.18/2.33  
% 6.18/2.33  Ordering : KBO
% 6.18/2.33  
% 6.18/2.33  Simplification rules
% 6.18/2.33  ----------------------
% 6.18/2.33  #Subsume      : 199
% 6.18/2.33  #Demod        : 1293
% 6.18/2.33  #Tautology    : 1377
% 6.18/2.33  #SimpNegUnit  : 70
% 6.18/2.33  #BackRed      : 78
% 6.18/2.33  
% 6.18/2.33  #Partial instantiations: 0
% 6.18/2.33  #Strategies tried      : 1
% 6.18/2.33  
% 6.18/2.33  Timing (in seconds)
% 6.18/2.33  ----------------------
% 6.18/2.33  Preprocessing        : 0.38
% 6.18/2.33  Parsing              : 0.19
% 6.18/2.33  CNF conversion       : 0.03
% 6.18/2.33  Main loop            : 1.11
% 6.18/2.33  Inferencing          : 0.41
% 6.18/2.33  Reduction            : 0.40
% 6.18/2.33  Demodulation         : 0.29
% 6.18/2.33  BG Simplification    : 0.05
% 6.18/2.33  Subsumption          : 0.16
% 6.18/2.33  Abstraction          : 0.06
% 6.18/2.33  MUC search           : 0.00
% 6.18/2.33  Cooper               : 0.00
% 6.18/2.33  Total                : 1.55
% 6.18/2.33  Index Insertion      : 0.00
% 6.18/2.34  Index Deletion       : 0.00
% 6.18/2.34  Index Matching       : 0.00
% 6.18/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
