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
% DateTime   : Thu Dec  3 09:44:25 EST 2020

% Result     : Theorem 12.91s
% Output     : CNFRefutation 13.10s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 332 expanded)
%              Number of leaves         :   20 ( 119 expanded)
%              Depth                    :   13
%              Number of atoms          :  151 ( 541 expanded)
%              Number of equality atoms :   89 ( 259 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(A,B)
      <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_74,plain,(
    ! [A_25,B_26] :
      ( r1_xboole_0(A_25,B_26)
      | k3_xboole_0(A_25,B_26) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_39,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_80,plain,(
    k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_74,c_39])).

tff(c_85,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_80])).

tff(c_16,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22766,plain,(
    ! [A_305,B_306] : k4_xboole_0(A_305,k4_xboole_0(A_305,B_306)) = k3_xboole_0(A_305,B_306) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22788,plain,(
    ! [A_307] : k4_xboole_0(A_307,A_307) = k3_xboole_0(A_307,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22766])).

tff(c_22798,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_22788,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22833,plain,(
    ! [A_310,B_311,C_312] :
      ( ~ r1_xboole_0(A_310,B_311)
      | ~ r2_hidden(C_312,B_311)
      | ~ r2_hidden(C_312,A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23352,plain,(
    ! [C_328,B_329,A_330] :
      ( ~ r2_hidden(C_328,B_329)
      | ~ r2_hidden(C_328,A_330)
      | k3_xboole_0(A_330,B_329) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_22833])).

tff(c_25284,plain,(
    ! [A_358,B_359,A_360] :
      ( ~ r2_hidden('#skF_1'(A_358,B_359),A_360)
      | k3_xboole_0(A_360,B_359) != k1_xboole_0
      | r1_xboole_0(A_358,B_359) ) ),
    inference(resolution,[status(thm)],[c_12,c_23352])).

tff(c_25293,plain,(
    ! [B_361,A_362] :
      ( k3_xboole_0(B_361,B_361) != k1_xboole_0
      | r1_xboole_0(A_362,B_361) ) ),
    inference(resolution,[status(thm)],[c_12,c_25284])).

tff(c_25310,plain,(
    ! [A_363] : r1_xboole_0(A_363,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_22798,c_25293])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25319,plain,(
    ! [A_363] : k3_xboole_0(A_363,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25310,c_4])).

tff(c_22784,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_22766])).

tff(c_140,plain,(
    ! [A_31,B_32] : k4_xboole_0(A_31,k4_xboole_0(A_31,B_32)) = k3_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [A_33] : k4_xboole_0(A_33,A_33) = k3_xboole_0(A_33,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_140])).

tff(c_168,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_16])).

tff(c_12505,plain,(
    ! [A_189,B_190,C_191] :
      ( ~ r1_xboole_0(A_189,B_190)
      | ~ r2_hidden(C_191,B_190)
      | ~ r2_hidden(C_191,A_189) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_14256,plain,(
    ! [C_223,B_224,A_225] :
      ( ~ r2_hidden(C_223,B_224)
      | ~ r2_hidden(C_223,A_225)
      | k3_xboole_0(A_225,B_224) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_12505])).

tff(c_22583,plain,(
    ! [A_293,B_294,A_295] :
      ( ~ r2_hidden('#skF_1'(A_293,B_294),A_295)
      | k3_xboole_0(A_295,B_294) != k1_xboole_0
      | r1_xboole_0(A_293,B_294) ) ),
    inference(resolution,[status(thm)],[c_12,c_14256])).

tff(c_22592,plain,(
    ! [B_296,A_297] :
      ( k3_xboole_0(B_296,B_296) != k1_xboole_0
      | r1_xboole_0(A_297,B_296) ) ),
    inference(resolution,[status(thm)],[c_12,c_22583])).

tff(c_22606,plain,(
    ! [A_298] : r1_xboole_0(A_298,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_22592])).

tff(c_22615,plain,(
    ! [A_298] : k3_xboole_0(A_298,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22606,c_4])).

tff(c_155,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_140])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_182,plain,(
    k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_224,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,B_40)
      | ~ r2_hidden(C_41,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_453,plain,(
    ! [C_51,B_52,A_53] :
      ( ~ r2_hidden(C_51,B_52)
      | ~ r2_hidden(C_51,A_53)
      | k3_xboole_0(A_53,B_52) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_224])).

tff(c_4979,plain,(
    ! [A_104,B_105,A_106] :
      ( ~ r2_hidden('#skF_1'(A_104,B_105),A_106)
      | k3_xboole_0(A_106,B_105) != k1_xboole_0
      | r1_xboole_0(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_12,c_453])).

tff(c_4988,plain,(
    ! [B_107,A_108] :
      ( k3_xboole_0(B_107,B_107) != k1_xboole_0
      | r1_xboole_0(A_108,B_107) ) ),
    inference(resolution,[status(thm)],[c_12,c_4979])).

tff(c_5005,plain,(
    ! [A_109] : r1_xboole_0(A_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_4988])).

tff(c_5014,plain,(
    ! [A_109] : k3_xboole_0(A_109,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_5005,c_4])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_164,plain,(
    ! [A_33] : k4_xboole_0(A_33,k3_xboole_0(A_33,k1_xboole_0)) = k3_xboole_0(A_33,A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_18])).

tff(c_5146,plain,(
    ! [A_33] : k4_xboole_0(A_33,k1_xboole_0) = k3_xboole_0(A_33,A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5014,c_164])).

tff(c_5381,plain,(
    ! [A_114] : k3_xboole_0(A_114,A_114) = A_114 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_5146])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k4_xboole_0(k3_xboole_0(A_15,B_16),C_17) = k3_xboole_0(A_15,k4_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12183,plain,(
    ! [A_183,C_184] : k3_xboole_0(A_183,k4_xboole_0(A_183,C_184)) = k4_xboole_0(A_183,C_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_5381,c_20])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_87,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_93,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_759,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k3_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,k4_xboole_0(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_18])).

tff(c_845,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_93,c_759])).

tff(c_868,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_845])).

tff(c_12283,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_12183,c_868])).

tff(c_12392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_182,c_12283])).

tff(c_12393,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_12617,plain,(
    ! [A_197,B_198,C_199] : k4_xboole_0(k3_xboole_0(A_197,B_198),C_199) = k3_xboole_0(A_197,k4_xboole_0(B_198,C_199)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_13321,plain,(
    ! [A_210,B_211,C_212] : k4_xboole_0(k3_xboole_0(A_210,B_211),C_212) = k3_xboole_0(B_211,k4_xboole_0(A_210,C_212)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_12617])).

tff(c_17146,plain,(
    ! [B_254,A_255,C_256] : k3_xboole_0(B_254,k4_xboole_0(A_255,C_256)) = k3_xboole_0(A_255,k4_xboole_0(B_254,C_256)) ),
    inference(superposition,[status(thm),theory(equality)],[c_13321,c_20])).

tff(c_17905,plain,(
    ! [A_259] : k3_xboole_0('#skF_2',k4_xboole_0(A_259,'#skF_3')) = k3_xboole_0(A_259,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12393,c_17146])).

tff(c_17960,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_17905])).

tff(c_22726,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22615,c_22615,c_17960])).

tff(c_22737,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_22726])).

tff(c_22738,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_22919,plain,(
    ! [A_317,B_318,C_319] : k4_xboole_0(k3_xboole_0(A_317,B_318),C_319) = k3_xboole_0(A_317,k4_xboole_0(B_318,C_319)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_23245,plain,(
    ! [A_325,B_326,C_327] : k4_xboole_0(k3_xboole_0(A_325,B_326),C_327) = k3_xboole_0(B_326,k4_xboole_0(A_325,C_327)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22919])).

tff(c_23360,plain,(
    ! [B_331,A_332,C_333] : k3_xboole_0(B_331,k4_xboole_0(A_332,C_333)) = k3_xboole_0(A_332,k4_xboole_0(B_331,C_333)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_23245])).

tff(c_23681,plain,(
    ! [B_337] : k3_xboole_0('#skF_2',k4_xboole_0(B_337,'#skF_3')) = k3_xboole_0(B_337,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22738,c_23360])).

tff(c_23727,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3',k1_xboole_0)) = k3_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_22784,c_23681])).

tff(c_25395,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_25319,c_25319,c_23727])).

tff(c_25402,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_25395])).

tff(c_25404,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_22,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_25490,plain,(
    k4_xboole_0('#skF_4','#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_25404,c_22])).

tff(c_25537,plain,(
    ! [A_376,B_377] : k4_xboole_0(A_376,k4_xboole_0(A_376,B_377)) = k3_xboole_0(A_376,B_377) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25555,plain,(
    ! [A_378] : k4_xboole_0(A_378,A_378) = k3_xboole_0(A_378,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_25537])).

tff(c_25565,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_25555,c_16])).

tff(c_25662,plain,(
    ! [A_385,B_386,C_387] :
      ( ~ r1_xboole_0(A_385,B_386)
      | ~ r2_hidden(C_387,B_386)
      | ~ r2_hidden(C_387,A_385) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_26269,plain,(
    ! [C_405,B_406,A_407] :
      ( ~ r2_hidden(C_405,B_406)
      | ~ r2_hidden(C_405,A_407)
      | k3_xboole_0(A_407,B_406) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_25662])).

tff(c_28499,plain,(
    ! [A_437,B_438,A_439] :
      ( ~ r2_hidden('#skF_1'(A_437,B_438),A_439)
      | k3_xboole_0(A_439,B_438) != k1_xboole_0
      | r1_xboole_0(A_437,B_438) ) ),
    inference(resolution,[status(thm)],[c_12,c_26269])).

tff(c_28508,plain,(
    ! [B_440,A_441] :
      ( k3_xboole_0(B_440,B_440) != k1_xboole_0
      | r1_xboole_0(A_441,B_440) ) ),
    inference(resolution,[status(thm)],[c_12,c_28499])).

tff(c_28527,plain,(
    ! [A_442] : r1_xboole_0(A_442,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25565,c_28508])).

tff(c_28536,plain,(
    ! [A_442] : k3_xboole_0(A_442,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28527,c_4])).

tff(c_25710,plain,(
    ! [A_391,B_392,C_393] : k4_xboole_0(k3_xboole_0(A_391,B_392),C_393) = k3_xboole_0(A_391,k4_xboole_0(B_392,C_393)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_25961,plain,(
    ! [C_401] : k3_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,C_401)) = k4_xboole_0(k1_xboole_0,C_401) ),
    inference(superposition,[status(thm),theory(equality)],[c_25565,c_25710])).

tff(c_25991,plain,(
    ! [B_14] : k4_xboole_0(k1_xboole_0,k4_xboole_0(k1_xboole_0,B_14)) = k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_25961])).

tff(c_26221,plain,(
    ! [B_404] : k3_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_404)) = k3_xboole_0(k1_xboole_0,B_404) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_25991])).

tff(c_26258,plain,(
    ! [A_1] : k3_xboole_0(k1_xboole_0,k3_xboole_0(A_1,k1_xboole_0)) = k3_xboole_0(k1_xboole_0,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26221])).

tff(c_28628,plain,(
    ! [A_1] : k3_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28536,c_28536,c_26258])).

tff(c_25581,plain,(
    ! [A_381] : k4_xboole_0(A_381,k3_xboole_0(A_381,k1_xboole_0)) = k3_xboole_0(A_381,A_381) ),
    inference(superposition,[status(thm),theory(equality)],[c_25555,c_18])).

tff(c_25601,plain,(
    ! [B_2] : k4_xboole_0(B_2,k3_xboole_0(k1_xboole_0,B_2)) = k3_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25581])).

tff(c_28791,plain,(
    ! [B_2] : k4_xboole_0(B_2,k1_xboole_0) = k3_xboole_0(B_2,B_2) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28628,c_25601])).

tff(c_29050,plain,(
    ! [B_449] : k3_xboole_0(B_449,B_449) = B_449 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_28791])).

tff(c_25773,plain,(
    ! [B_2,A_1,C_393] : k4_xboole_0(k3_xboole_0(B_2,A_1),C_393) = k3_xboole_0(A_1,k4_xboole_0(B_2,C_393)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_25710])).

tff(c_38705,plain,(
    ! [B_541,C_542] : k3_xboole_0(B_541,k4_xboole_0(B_541,C_542)) = k4_xboole_0(B_541,C_542) ),
    inference(superposition,[status(thm),theory(equality)],[c_29050,c_25773])).

tff(c_25403,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_25452,plain,(
    ! [A_368,B_369] :
      ( k3_xboole_0(A_368,B_369) = k1_xboole_0
      | ~ r1_xboole_0(A_368,B_369) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_25468,plain,(
    k3_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_25403,c_25452])).

tff(c_26005,plain,(
    ! [A_402,B_403] : k4_xboole_0(A_402,k3_xboole_0(A_402,B_403)) = k3_xboole_0(A_402,k4_xboole_0(A_402,B_403)) ),
    inference(superposition,[status(thm),theory(equality)],[c_25537,c_18])).

tff(c_26084,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = k4_xboole_0('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_25468,c_26005])).

tff(c_26107,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_4','#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26084])).

tff(c_38827,plain,(
    k4_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_38705,c_26107])).

tff(c_38938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25490,c_38827])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:25:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.91/5.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.91/5.87  
% 12.91/5.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.91/5.88  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 12.91/5.88  
% 12.91/5.88  %Foreground sorts:
% 12.91/5.88  
% 12.91/5.88  
% 12.91/5.88  %Background operators:
% 12.91/5.88  
% 12.91/5.88  
% 12.91/5.88  %Foreground operators:
% 12.91/5.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.91/5.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.91/5.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.91/5.88  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.91/5.88  tff('#skF_5', type, '#skF_5': $i).
% 12.91/5.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.91/5.88  tff('#skF_2', type, '#skF_2': $i).
% 12.91/5.88  tff('#skF_3', type, '#skF_3': $i).
% 12.91/5.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.91/5.88  tff('#skF_4', type, '#skF_4': $i).
% 12.91/5.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.91/5.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.91/5.88  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 12.91/5.88  
% 13.10/5.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.10/5.90  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 13.10/5.90  tff(f_64, negated_conjecture, ~(![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 13.10/5.90  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 13.10/5.90  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 13.10/5.90  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 13.10/5.90  tff(f_59, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 13.10/5.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.10/5.90  tff(c_74, plain, (![A_25, B_26]: (r1_xboole_0(A_25, B_26) | k3_xboole_0(A_25, B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.10/5.90  tff(c_26, plain, (~r1_xboole_0('#skF_2', '#skF_3') | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.10/5.90  tff(c_39, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_26])).
% 13.10/5.90  tff(c_80, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_74, c_39])).
% 13.10/5.90  tff(c_85, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_80])).
% 13.10/5.90  tff(c_16, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_55])).
% 13.10/5.90  tff(c_22766, plain, (![A_305, B_306]: (k4_xboole_0(A_305, k4_xboole_0(A_305, B_306))=k3_xboole_0(A_305, B_306))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.10/5.90  tff(c_22788, plain, (![A_307]: (k4_xboole_0(A_307, A_307)=k3_xboole_0(A_307, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22766])).
% 13.10/5.90  tff(c_22798, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_22788, c_16])).
% 13.10/5.90  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.10/5.90  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.10/5.90  tff(c_22833, plain, (![A_310, B_311, C_312]: (~r1_xboole_0(A_310, B_311) | ~r2_hidden(C_312, B_311) | ~r2_hidden(C_312, A_310))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.10/5.90  tff(c_23352, plain, (![C_328, B_329, A_330]: (~r2_hidden(C_328, B_329) | ~r2_hidden(C_328, A_330) | k3_xboole_0(A_330, B_329)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_22833])).
% 13.10/5.90  tff(c_25284, plain, (![A_358, B_359, A_360]: (~r2_hidden('#skF_1'(A_358, B_359), A_360) | k3_xboole_0(A_360, B_359)!=k1_xboole_0 | r1_xboole_0(A_358, B_359))), inference(resolution, [status(thm)], [c_12, c_23352])).
% 13.10/5.90  tff(c_25293, plain, (![B_361, A_362]: (k3_xboole_0(B_361, B_361)!=k1_xboole_0 | r1_xboole_0(A_362, B_361))), inference(resolution, [status(thm)], [c_12, c_25284])).
% 13.10/5.90  tff(c_25310, plain, (![A_363]: (r1_xboole_0(A_363, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_22798, c_25293])).
% 13.10/5.90  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.10/5.90  tff(c_25319, plain, (![A_363]: (k3_xboole_0(A_363, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_25310, c_4])).
% 13.10/5.90  tff(c_22784, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_22766])).
% 13.10/5.90  tff(c_140, plain, (![A_31, B_32]: (k4_xboole_0(A_31, k4_xboole_0(A_31, B_32))=k3_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.10/5.90  tff(c_158, plain, (![A_33]: (k4_xboole_0(A_33, A_33)=k3_xboole_0(A_33, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_140])).
% 13.10/5.90  tff(c_168, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_158, c_16])).
% 13.10/5.90  tff(c_12505, plain, (![A_189, B_190, C_191]: (~r1_xboole_0(A_189, B_190) | ~r2_hidden(C_191, B_190) | ~r2_hidden(C_191, A_189))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.10/5.90  tff(c_14256, plain, (![C_223, B_224, A_225]: (~r2_hidden(C_223, B_224) | ~r2_hidden(C_223, A_225) | k3_xboole_0(A_225, B_224)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_12505])).
% 13.10/5.90  tff(c_22583, plain, (![A_293, B_294, A_295]: (~r2_hidden('#skF_1'(A_293, B_294), A_295) | k3_xboole_0(A_295, B_294)!=k1_xboole_0 | r1_xboole_0(A_293, B_294))), inference(resolution, [status(thm)], [c_12, c_14256])).
% 13.10/5.90  tff(c_22592, plain, (![B_296, A_297]: (k3_xboole_0(B_296, B_296)!=k1_xboole_0 | r1_xboole_0(A_297, B_296))), inference(resolution, [status(thm)], [c_12, c_22583])).
% 13.10/5.90  tff(c_22606, plain, (![A_298]: (r1_xboole_0(A_298, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_22592])).
% 13.10/5.90  tff(c_22615, plain, (![A_298]: (k3_xboole_0(A_298, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_22606, c_4])).
% 13.10/5.90  tff(c_155, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_140])).
% 13.10/5.90  tff(c_24, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2' | k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.10/5.90  tff(c_182, plain, (k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 13.10/5.90  tff(c_224, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, B_40) | ~r2_hidden(C_41, A_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.10/5.90  tff(c_453, plain, (![C_51, B_52, A_53]: (~r2_hidden(C_51, B_52) | ~r2_hidden(C_51, A_53) | k3_xboole_0(A_53, B_52)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_224])).
% 13.10/5.90  tff(c_4979, plain, (![A_104, B_105, A_106]: (~r2_hidden('#skF_1'(A_104, B_105), A_106) | k3_xboole_0(A_106, B_105)!=k1_xboole_0 | r1_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_12, c_453])).
% 13.10/5.90  tff(c_4988, plain, (![B_107, A_108]: (k3_xboole_0(B_107, B_107)!=k1_xboole_0 | r1_xboole_0(A_108, B_107))), inference(resolution, [status(thm)], [c_12, c_4979])).
% 13.10/5.90  tff(c_5005, plain, (![A_109]: (r1_xboole_0(A_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_168, c_4988])).
% 13.10/5.90  tff(c_5014, plain, (![A_109]: (k3_xboole_0(A_109, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_5005, c_4])).
% 13.10/5.90  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.10/5.90  tff(c_164, plain, (![A_33]: (k4_xboole_0(A_33, k3_xboole_0(A_33, k1_xboole_0))=k3_xboole_0(A_33, A_33))), inference(superposition, [status(thm), theory('equality')], [c_158, c_18])).
% 13.10/5.90  tff(c_5146, plain, (![A_33]: (k4_xboole_0(A_33, k1_xboole_0)=k3_xboole_0(A_33, A_33))), inference(demodulation, [status(thm), theory('equality')], [c_5014, c_164])).
% 13.10/5.90  tff(c_5381, plain, (![A_114]: (k3_xboole_0(A_114, A_114)=A_114)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_5146])).
% 13.10/5.90  tff(c_20, plain, (![A_15, B_16, C_17]: (k4_xboole_0(k3_xboole_0(A_15, B_16), C_17)=k3_xboole_0(A_15, k4_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.10/5.90  tff(c_12183, plain, (![A_183, C_184]: (k3_xboole_0(A_183, k4_xboole_0(A_183, C_184))=k4_xboole_0(A_183, C_184))), inference(superposition, [status(thm), theory('equality')], [c_5381, c_20])).
% 13.10/5.90  tff(c_28, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2' | r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.10/5.90  tff(c_87, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_28])).
% 13.10/5.90  tff(c_93, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_87, c_4])).
% 13.10/5.90  tff(c_759, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k3_xboole_0(A_61, B_62))=k3_xboole_0(A_61, k4_xboole_0(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_18])).
% 13.10/5.90  tff(c_845, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_93, c_759])).
% 13.10/5.90  tff(c_868, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_845])).
% 13.10/5.90  tff(c_12283, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_12183, c_868])).
% 13.10/5.90  tff(c_12392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_182, c_12283])).
% 13.10/5.90  tff(c_12393, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 13.10/5.90  tff(c_12617, plain, (![A_197, B_198, C_199]: (k4_xboole_0(k3_xboole_0(A_197, B_198), C_199)=k3_xboole_0(A_197, k4_xboole_0(B_198, C_199)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.10/5.90  tff(c_13321, plain, (![A_210, B_211, C_212]: (k4_xboole_0(k3_xboole_0(A_210, B_211), C_212)=k3_xboole_0(B_211, k4_xboole_0(A_210, C_212)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_12617])).
% 13.10/5.90  tff(c_17146, plain, (![B_254, A_255, C_256]: (k3_xboole_0(B_254, k4_xboole_0(A_255, C_256))=k3_xboole_0(A_255, k4_xboole_0(B_254, C_256)))), inference(superposition, [status(thm), theory('equality')], [c_13321, c_20])).
% 13.10/5.90  tff(c_17905, plain, (![A_259]: (k3_xboole_0('#skF_2', k4_xboole_0(A_259, '#skF_3'))=k3_xboole_0(A_259, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_12393, c_17146])).
% 13.10/5.90  tff(c_17960, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_155, c_17905])).
% 13.10/5.90  tff(c_22726, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_22615, c_22615, c_17960])).
% 13.10/5.90  tff(c_22737, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_22726])).
% 13.10/5.90  tff(c_22738, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 13.10/5.90  tff(c_22919, plain, (![A_317, B_318, C_319]: (k4_xboole_0(k3_xboole_0(A_317, B_318), C_319)=k3_xboole_0(A_317, k4_xboole_0(B_318, C_319)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.10/5.90  tff(c_23245, plain, (![A_325, B_326, C_327]: (k4_xboole_0(k3_xboole_0(A_325, B_326), C_327)=k3_xboole_0(B_326, k4_xboole_0(A_325, C_327)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22919])).
% 13.10/5.90  tff(c_23360, plain, (![B_331, A_332, C_333]: (k3_xboole_0(B_331, k4_xboole_0(A_332, C_333))=k3_xboole_0(A_332, k4_xboole_0(B_331, C_333)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_23245])).
% 13.10/5.90  tff(c_23681, plain, (![B_337]: (k3_xboole_0('#skF_2', k4_xboole_0(B_337, '#skF_3'))=k3_xboole_0(B_337, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_22738, c_23360])).
% 13.10/5.90  tff(c_23727, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', k1_xboole_0))=k3_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_22784, c_23681])).
% 13.10/5.90  tff(c_25395, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_25319, c_25319, c_23727])).
% 13.10/5.90  tff(c_25402, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_25395])).
% 13.10/5.90  tff(c_25404, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 13.10/5.90  tff(c_22, plain, (~r1_xboole_0('#skF_2', '#skF_3') | k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 13.10/5.90  tff(c_25490, plain, (k4_xboole_0('#skF_4', '#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_25404, c_22])).
% 13.10/5.90  tff(c_25537, plain, (![A_376, B_377]: (k4_xboole_0(A_376, k4_xboole_0(A_376, B_377))=k3_xboole_0(A_376, B_377))), inference(cnfTransformation, [status(thm)], [f_57])).
% 13.10/5.90  tff(c_25555, plain, (![A_378]: (k4_xboole_0(A_378, A_378)=k3_xboole_0(A_378, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_25537])).
% 13.10/5.90  tff(c_25565, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_25555, c_16])).
% 13.10/5.90  tff(c_25662, plain, (![A_385, B_386, C_387]: (~r1_xboole_0(A_385, B_386) | ~r2_hidden(C_387, B_386) | ~r2_hidden(C_387, A_385))), inference(cnfTransformation, [status(thm)], [f_53])).
% 13.10/5.90  tff(c_26269, plain, (![C_405, B_406, A_407]: (~r2_hidden(C_405, B_406) | ~r2_hidden(C_405, A_407) | k3_xboole_0(A_407, B_406)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_25662])).
% 13.10/5.90  tff(c_28499, plain, (![A_437, B_438, A_439]: (~r2_hidden('#skF_1'(A_437, B_438), A_439) | k3_xboole_0(A_439, B_438)!=k1_xboole_0 | r1_xboole_0(A_437, B_438))), inference(resolution, [status(thm)], [c_12, c_26269])).
% 13.10/5.90  tff(c_28508, plain, (![B_440, A_441]: (k3_xboole_0(B_440, B_440)!=k1_xboole_0 | r1_xboole_0(A_441, B_440))), inference(resolution, [status(thm)], [c_12, c_28499])).
% 13.10/5.90  tff(c_28527, plain, (![A_442]: (r1_xboole_0(A_442, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_25565, c_28508])).
% 13.10/5.90  tff(c_28536, plain, (![A_442]: (k3_xboole_0(A_442, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_28527, c_4])).
% 13.10/5.90  tff(c_25710, plain, (![A_391, B_392, C_393]: (k4_xboole_0(k3_xboole_0(A_391, B_392), C_393)=k3_xboole_0(A_391, k4_xboole_0(B_392, C_393)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.10/5.90  tff(c_25961, plain, (![C_401]: (k3_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, C_401))=k4_xboole_0(k1_xboole_0, C_401))), inference(superposition, [status(thm), theory('equality')], [c_25565, c_25710])).
% 13.10/5.90  tff(c_25991, plain, (![B_14]: (k4_xboole_0(k1_xboole_0, k4_xboole_0(k1_xboole_0, B_14))=k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_25961])).
% 13.10/5.90  tff(c_26221, plain, (![B_404]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_404))=k3_xboole_0(k1_xboole_0, B_404))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_25991])).
% 13.10/5.90  tff(c_26258, plain, (![A_1]: (k3_xboole_0(k1_xboole_0, k3_xboole_0(A_1, k1_xboole_0))=k3_xboole_0(k1_xboole_0, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_26221])).
% 13.10/5.90  tff(c_28628, plain, (![A_1]: (k3_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28536, c_28536, c_26258])).
% 13.10/5.90  tff(c_25581, plain, (![A_381]: (k4_xboole_0(A_381, k3_xboole_0(A_381, k1_xboole_0))=k3_xboole_0(A_381, A_381))), inference(superposition, [status(thm), theory('equality')], [c_25555, c_18])).
% 13.10/5.90  tff(c_25601, plain, (![B_2]: (k4_xboole_0(B_2, k3_xboole_0(k1_xboole_0, B_2))=k3_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_25581])).
% 13.10/5.90  tff(c_28791, plain, (![B_2]: (k4_xboole_0(B_2, k1_xboole_0)=k3_xboole_0(B_2, B_2))), inference(demodulation, [status(thm), theory('equality')], [c_28628, c_25601])).
% 13.10/5.90  tff(c_29050, plain, (![B_449]: (k3_xboole_0(B_449, B_449)=B_449)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_28791])).
% 13.10/5.90  tff(c_25773, plain, (![B_2, A_1, C_393]: (k4_xboole_0(k3_xboole_0(B_2, A_1), C_393)=k3_xboole_0(A_1, k4_xboole_0(B_2, C_393)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_25710])).
% 13.10/5.90  tff(c_38705, plain, (![B_541, C_542]: (k3_xboole_0(B_541, k4_xboole_0(B_541, C_542))=k4_xboole_0(B_541, C_542))), inference(superposition, [status(thm), theory('equality')], [c_29050, c_25773])).
% 13.10/5.90  tff(c_25403, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 13.10/5.90  tff(c_25452, plain, (![A_368, B_369]: (k3_xboole_0(A_368, B_369)=k1_xboole_0 | ~r1_xboole_0(A_368, B_369))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.10/5.90  tff(c_25468, plain, (k3_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_25403, c_25452])).
% 13.10/5.90  tff(c_26005, plain, (![A_402, B_403]: (k4_xboole_0(A_402, k3_xboole_0(A_402, B_403))=k3_xboole_0(A_402, k4_xboole_0(A_402, B_403)))), inference(superposition, [status(thm), theory('equality')], [c_25537, c_18])).
% 13.10/5.90  tff(c_26084, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))=k4_xboole_0('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_25468, c_26005])).
% 13.10/5.90  tff(c_26107, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_4', '#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26084])).
% 13.10/5.90  tff(c_38827, plain, (k4_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_38705, c_26107])).
% 13.10/5.90  tff(c_38938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25490, c_38827])).
% 13.10/5.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.10/5.90  
% 13.10/5.90  Inference rules
% 13.10/5.90  ----------------------
% 13.10/5.90  #Ref     : 0
% 13.10/5.90  #Sup     : 9585
% 13.10/5.90  #Fact    : 0
% 13.10/5.90  #Define  : 0
% 13.10/5.90  #Split   : 12
% 13.10/5.90  #Chain   : 0
% 13.10/5.90  #Close   : 0
% 13.10/5.90  
% 13.10/5.90  Ordering : KBO
% 13.10/5.90  
% 13.10/5.90  Simplification rules
% 13.10/5.90  ----------------------
% 13.10/5.90  #Subsume      : 265
% 13.10/5.90  #Demod        : 15040
% 13.10/5.90  #Tautology    : 5426
% 13.10/5.90  #SimpNegUnit  : 14
% 13.10/5.90  #BackRed      : 134
% 13.10/5.90  
% 13.10/5.90  #Partial instantiations: 0
% 13.10/5.90  #Strategies tried      : 1
% 13.10/5.90  
% 13.10/5.90  Timing (in seconds)
% 13.10/5.90  ----------------------
% 13.10/5.90  Preprocessing        : 0.28
% 13.10/5.90  Parsing              : 0.15
% 13.10/5.90  CNF conversion       : 0.02
% 13.10/5.90  Main loop            : 4.77
% 13.10/5.90  Inferencing          : 0.88
% 13.10/5.90  Reduction            : 3.04
% 13.10/5.90  Demodulation         : 2.77
% 13.10/5.90  BG Simplification    : 0.12
% 13.10/5.90  Subsumption          : 0.54
% 13.10/5.90  Abstraction          : 0.19
% 13.10/5.90  MUC search           : 0.00
% 13.10/5.90  Cooper               : 0.00
% 13.10/5.90  Total                : 5.10
% 13.10/5.90  Index Insertion      : 0.00
% 13.10/5.90  Index Deletion       : 0.00
% 13.10/5.90  Index Matching       : 0.00
% 13.10/5.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
