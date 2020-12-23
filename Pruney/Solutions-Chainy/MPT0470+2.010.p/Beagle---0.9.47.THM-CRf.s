%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:02 EST 2020

% Result     : Theorem 3.17s
% Output     : CNFRefutation 3.26s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 161 expanded)
%              Number of leaves         :   39 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :  163 ( 282 expanded)
%              Number of equality atoms :   40 (  59 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_108,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k5_relat_1(k1_xboole_0,A) = k1_xboole_0
          & k5_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_101,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_98,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_38,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_77,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => ( C = k5_relat_1(A,B)
              <=> ! [D,E] :
                    ( r2_hidden(k4_tarski(D,E),C)
                  <=> ? [F] :
                        ( r2_hidden(k4_tarski(D,F),A)
                        & r2_hidden(k4_tarski(F,E),B) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_relat_1)).

tff(f_40,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_60,plain,
    ( k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0
    | k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_92,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_62,plain,(
    v1_relat_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_87,plain,(
    ! [A_133] :
      ( v1_relat_1(A_133)
      | ~ v1_xboole_0(A_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_91,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_87])).

tff(c_50,plain,(
    ! [A_123,B_124] :
      ( v1_relat_1(k5_relat_1(A_123,B_124))
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(A_123) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_56,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_189,plain,(
    ! [A_155,B_156] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_155,B_156)),k2_relat_1(B_156))
      | ~ v1_relat_1(B_156)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_194,plain,(
    ! [A_155] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_155,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_155) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_189])).

tff(c_198,plain,(
    ! [A_157] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_157,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_157) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_194])).

tff(c_12,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_117,plain,(
    ! [B_138,A_139] :
      ( B_138 = A_139
      | ~ r1_tarski(B_138,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_126,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_117])).

tff(c_217,plain,(
    ! [A_163] :
      ( k2_relat_1(k5_relat_1(A_163,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_163) ) ),
    inference(resolution,[status(thm)],[c_198,c_126])).

tff(c_52,plain,(
    ! [A_125] :
      ( ~ v1_xboole_0(k2_relat_1(A_125))
      | ~ v1_relat_1(A_125)
      | v1_xboole_0(A_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_232,plain,(
    ! [A_163] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_163,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_163,k1_xboole_0))
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_52])).

tff(c_243,plain,(
    ! [A_164] :
      ( ~ v1_relat_1(k5_relat_1(A_164,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_164,k1_xboole_0))
      | ~ v1_relat_1(A_164) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_232])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_253,plain,(
    ! [A_170] :
      ( k5_relat_1(A_170,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_170,k1_xboole_0))
      | ~ v1_relat_1(A_170) ) ),
    inference(resolution,[status(thm)],[c_243,c_4])).

tff(c_257,plain,(
    ! [A_123] :
      ( k5_relat_1(A_123,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_50,c_253])).

tff(c_261,plain,(
    ! [A_171] :
      ( k5_relat_1(A_171,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_171) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_257])).

tff(c_272,plain,(
    k5_relat_1(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91,c_261])).

tff(c_650,plain,(
    ! [A_198,B_199,C_200] :
      ( r2_hidden(k4_tarski('#skF_4'(A_198,B_199,C_200),'#skF_3'(A_198,B_199,C_200)),B_199)
      | r2_hidden(k4_tarski('#skF_5'(A_198,B_199,C_200),'#skF_6'(A_198,B_199,C_200)),C_200)
      | k5_relat_1(A_198,B_199) = C_200
      | ~ v1_relat_1(C_200)
      | ~ v1_relat_1(B_199)
      | ~ v1_relat_1(A_198) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_14,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_160,plain,(
    ! [B_145,A_146] :
      ( ~ r2_hidden(B_145,A_146)
      | k4_xboole_0(A_146,k1_tarski(B_145)) != A_146 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_169,plain,(
    ! [B_145] : ~ r2_hidden(B_145,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_160])).

tff(c_664,plain,(
    ! [A_198,C_200] :
      ( r2_hidden(k4_tarski('#skF_5'(A_198,k1_xboole_0,C_200),'#skF_6'(A_198,k1_xboole_0,C_200)),C_200)
      | k5_relat_1(A_198,k1_xboole_0) = C_200
      | ~ v1_relat_1(C_200)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_198) ) ),
    inference(resolution,[status(thm)],[c_650,c_169])).

tff(c_686,plain,(
    ! [A_201,C_202] :
      ( r2_hidden(k4_tarski('#skF_5'(A_201,k1_xboole_0,C_202),'#skF_6'(A_201,k1_xboole_0,C_202)),C_202)
      | k5_relat_1(A_201,k1_xboole_0) = C_202
      | ~ v1_relat_1(C_202)
      | ~ v1_relat_1(A_201) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_664])).

tff(c_383,plain,(
    ! [D_174,A_175,B_176,E_177] :
      ( r2_hidden(k4_tarski(D_174,'#skF_1'(k5_relat_1(A_175,B_176),B_176,A_175,E_177,D_174)),A_175)
      | ~ r2_hidden(k4_tarski(D_174,E_177),k5_relat_1(A_175,B_176))
      | ~ v1_relat_1(k5_relat_1(A_175,B_176))
      | ~ v1_relat_1(B_176)
      | ~ v1_relat_1(A_175) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_389,plain,(
    ! [D_174,E_177,B_176] :
      ( ~ r2_hidden(k4_tarski(D_174,E_177),k5_relat_1(k1_xboole_0,B_176))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_176))
      | ~ v1_relat_1(B_176)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_383,c_169])).

tff(c_402,plain,(
    ! [D_174,E_177,B_176] :
      ( ~ r2_hidden(k4_tarski(D_174,E_177),k5_relat_1(k1_xboole_0,B_176))
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_176))
      | ~ v1_relat_1(B_176) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_389])).

tff(c_759,plain,(
    ! [B_210,A_211] :
      ( ~ v1_relat_1(B_210)
      | k5_relat_1(k1_xboole_0,B_210) = k5_relat_1(A_211,k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(k1_xboole_0,B_210))
      | ~ v1_relat_1(A_211) ) ),
    inference(resolution,[status(thm)],[c_686,c_402])).

tff(c_764,plain,(
    ! [B_124,A_211] :
      ( k5_relat_1(k1_xboole_0,B_124) = k5_relat_1(A_211,k1_xboole_0)
      | ~ v1_relat_1(A_211)
      | ~ v1_relat_1(B_124)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_50,c_759])).

tff(c_770,plain,(
    ! [B_212,A_213] :
      ( k5_relat_1(k1_xboole_0,B_212) = k5_relat_1(A_213,k1_xboole_0)
      | ~ v1_relat_1(A_213)
      | ~ v1_relat_1(B_212) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_764])).

tff(c_774,plain,(
    ! [B_212] :
      ( k5_relat_1(k1_xboole_0,k1_xboole_0) = k5_relat_1(k1_xboole_0,B_212)
      | ~ v1_relat_1(B_212) ) ),
    inference(resolution,[status(thm)],[c_91,c_770])).

tff(c_782,plain,(
    ! [B_214] :
      ( k5_relat_1(k1_xboole_0,B_214) = k1_xboole_0
      | ~ v1_relat_1(B_214) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_774])).

tff(c_791,plain,(
    k5_relat_1(k1_xboole_0,'#skF_7') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_782])).

tff(c_798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_791])).

tff(c_799,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_899,plain,(
    ! [A_232,B_233] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_232,B_233)),k2_relat_1(B_233))
      | ~ v1_relat_1(B_233)
      | ~ v1_relat_1(A_232) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_907,plain,(
    ! [A_232] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_232,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_899])).

tff(c_913,plain,(
    ! [A_234] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_234,k1_xboole_0)),k1_xboole_0)
      | ~ v1_relat_1(A_234) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_907])).

tff(c_829,plain,(
    ! [B_219,A_220] :
      ( B_219 = A_220
      | ~ r1_tarski(B_219,A_220)
      | ~ r1_tarski(A_220,B_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_838,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_12,c_829])).

tff(c_923,plain,(
    ! [A_235] :
      ( k2_relat_1(k5_relat_1(A_235,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(A_235) ) ),
    inference(resolution,[status(thm)],[c_913,c_838])).

tff(c_938,plain,(
    ! [A_235] :
      ( ~ v1_xboole_0(k1_xboole_0)
      | ~ v1_relat_1(k5_relat_1(A_235,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_235,k1_xboole_0))
      | ~ v1_relat_1(A_235) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_923,c_52])).

tff(c_958,plain,(
    ! [A_240] :
      ( ~ v1_relat_1(k5_relat_1(A_240,k1_xboole_0))
      | v1_xboole_0(k5_relat_1(A_240,k1_xboole_0))
      | ~ v1_relat_1(A_240) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_938])).

tff(c_967,plain,(
    ! [A_241] :
      ( k5_relat_1(A_241,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k5_relat_1(A_241,k1_xboole_0))
      | ~ v1_relat_1(A_241) ) ),
    inference(resolution,[status(thm)],[c_958,c_4])).

tff(c_971,plain,(
    ! [A_123] :
      ( k5_relat_1(A_123,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_123) ) ),
    inference(resolution,[status(thm)],[c_50,c_967])).

tff(c_975,plain,(
    ! [A_242] :
      ( k5_relat_1(A_242,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_971])).

tff(c_984,plain,(
    k5_relat_1('#skF_7',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_62,c_975])).

tff(c_990,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_984])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:19:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.17/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.47  
% 3.17/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.47  %$ r2_hidden > r1_tarski > v1_xboole_0 > v1_relat_1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_1 > #skF_3
% 3.17/1.47  
% 3.17/1.47  %Foreground sorts:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Background operators:
% 3.17/1.47  
% 3.17/1.47  
% 3.17/1.47  %Foreground operators:
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.17/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.17/1.47  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.17/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.17/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.17/1.47  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.17/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.17/1.47  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.17/1.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.17/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.17/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.17/1.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.17/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.17/1.47  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.17/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.17/1.47  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.17/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.17/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.17/1.47  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.17/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.17/1.47  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.17/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.17/1.47  
% 3.26/1.49  tff(f_108, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k5_relat_1(k1_xboole_0, A) = k1_xboole_0) & (k5_relat_1(A, k1_xboole_0) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_relat_1)).
% 3.26/1.49  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.26/1.49  tff(f_59, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relat_1)).
% 3.26/1.49  tff(f_83, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 3.26/1.49  tff(f_101, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 3.26/1.49  tff(f_98, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 3.26/1.49  tff(f_38, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.26/1.49  tff(f_36, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.26/1.49  tff(f_91, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_relat_1)).
% 3.26/1.49  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.26/1.49  tff(f_77, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => ((C = k5_relat_1(A, B)) <=> (![D, E]: (r2_hidden(k4_tarski(D, E), C) <=> (?[F]: (r2_hidden(k4_tarski(D, F), A) & r2_hidden(k4_tarski(F, E), B)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_relat_1)).
% 3.26/1.49  tff(f_40, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.26/1.49  tff(f_55, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.26/1.49  tff(c_60, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0 | k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_92, plain, (k5_relat_1(k1_xboole_0, '#skF_7')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_60])).
% 3.26/1.49  tff(c_62, plain, (v1_relat_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.26/1.49  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.26/1.49  tff(c_87, plain, (![A_133]: (v1_relat_1(A_133) | ~v1_xboole_0(A_133))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.26/1.49  tff(c_91, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_87])).
% 3.26/1.49  tff(c_50, plain, (![A_123, B_124]: (v1_relat_1(k5_relat_1(A_123, B_124)) | ~v1_relat_1(B_124) | ~v1_relat_1(A_123))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.26/1.49  tff(c_56, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.26/1.49  tff(c_189, plain, (![A_155, B_156]: (r1_tarski(k2_relat_1(k5_relat_1(A_155, B_156)), k2_relat_1(B_156)) | ~v1_relat_1(B_156) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.26/1.49  tff(c_194, plain, (![A_155]: (r1_tarski(k2_relat_1(k5_relat_1(A_155, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_155))), inference(superposition, [status(thm), theory('equality')], [c_56, c_189])).
% 3.26/1.49  tff(c_198, plain, (![A_157]: (r1_tarski(k2_relat_1(k5_relat_1(A_157, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_157))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_194])).
% 3.26/1.49  tff(c_12, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.26/1.49  tff(c_117, plain, (![B_138, A_139]: (B_138=A_139 | ~r1_tarski(B_138, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.49  tff(c_126, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_117])).
% 3.26/1.49  tff(c_217, plain, (![A_163]: (k2_relat_1(k5_relat_1(A_163, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_163))), inference(resolution, [status(thm)], [c_198, c_126])).
% 3.26/1.49  tff(c_52, plain, (![A_125]: (~v1_xboole_0(k2_relat_1(A_125)) | ~v1_relat_1(A_125) | v1_xboole_0(A_125))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.26/1.49  tff(c_232, plain, (![A_163]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_163, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_163, k1_xboole_0)) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_217, c_52])).
% 3.26/1.49  tff(c_243, plain, (![A_164]: (~v1_relat_1(k5_relat_1(A_164, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_164, k1_xboole_0)) | ~v1_relat_1(A_164))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_232])).
% 3.26/1.49  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.26/1.49  tff(c_253, plain, (![A_170]: (k5_relat_1(A_170, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_170, k1_xboole_0)) | ~v1_relat_1(A_170))), inference(resolution, [status(thm)], [c_243, c_4])).
% 3.26/1.49  tff(c_257, plain, (![A_123]: (k5_relat_1(A_123, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_50, c_253])).
% 3.26/1.49  tff(c_261, plain, (![A_171]: (k5_relat_1(A_171, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_171))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_257])).
% 3.26/1.49  tff(c_272, plain, (k5_relat_1(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_91, c_261])).
% 3.26/1.49  tff(c_650, plain, (![A_198, B_199, C_200]: (r2_hidden(k4_tarski('#skF_4'(A_198, B_199, C_200), '#skF_3'(A_198, B_199, C_200)), B_199) | r2_hidden(k4_tarski('#skF_5'(A_198, B_199, C_200), '#skF_6'(A_198, B_199, C_200)), C_200) | k5_relat_1(A_198, B_199)=C_200 | ~v1_relat_1(C_200) | ~v1_relat_1(B_199) | ~v1_relat_1(A_198))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.49  tff(c_14, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.26/1.49  tff(c_160, plain, (![B_145, A_146]: (~r2_hidden(B_145, A_146) | k4_xboole_0(A_146, k1_tarski(B_145))!=A_146)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.26/1.49  tff(c_169, plain, (![B_145]: (~r2_hidden(B_145, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_160])).
% 3.26/1.49  tff(c_664, plain, (![A_198, C_200]: (r2_hidden(k4_tarski('#skF_5'(A_198, k1_xboole_0, C_200), '#skF_6'(A_198, k1_xboole_0, C_200)), C_200) | k5_relat_1(A_198, k1_xboole_0)=C_200 | ~v1_relat_1(C_200) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_198))), inference(resolution, [status(thm)], [c_650, c_169])).
% 3.26/1.49  tff(c_686, plain, (![A_201, C_202]: (r2_hidden(k4_tarski('#skF_5'(A_201, k1_xboole_0, C_202), '#skF_6'(A_201, k1_xboole_0, C_202)), C_202) | k5_relat_1(A_201, k1_xboole_0)=C_202 | ~v1_relat_1(C_202) | ~v1_relat_1(A_201))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_664])).
% 3.26/1.49  tff(c_383, plain, (![D_174, A_175, B_176, E_177]: (r2_hidden(k4_tarski(D_174, '#skF_1'(k5_relat_1(A_175, B_176), B_176, A_175, E_177, D_174)), A_175) | ~r2_hidden(k4_tarski(D_174, E_177), k5_relat_1(A_175, B_176)) | ~v1_relat_1(k5_relat_1(A_175, B_176)) | ~v1_relat_1(B_176) | ~v1_relat_1(A_175))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.26/1.49  tff(c_389, plain, (![D_174, E_177, B_176]: (~r2_hidden(k4_tarski(D_174, E_177), k5_relat_1(k1_xboole_0, B_176)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_176)) | ~v1_relat_1(B_176) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_383, c_169])).
% 3.26/1.49  tff(c_402, plain, (![D_174, E_177, B_176]: (~r2_hidden(k4_tarski(D_174, E_177), k5_relat_1(k1_xboole_0, B_176)) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_176)) | ~v1_relat_1(B_176))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_389])).
% 3.26/1.49  tff(c_759, plain, (![B_210, A_211]: (~v1_relat_1(B_210) | k5_relat_1(k1_xboole_0, B_210)=k5_relat_1(A_211, k1_xboole_0) | ~v1_relat_1(k5_relat_1(k1_xboole_0, B_210)) | ~v1_relat_1(A_211))), inference(resolution, [status(thm)], [c_686, c_402])).
% 3.26/1.49  tff(c_764, plain, (![B_124, A_211]: (k5_relat_1(k1_xboole_0, B_124)=k5_relat_1(A_211, k1_xboole_0) | ~v1_relat_1(A_211) | ~v1_relat_1(B_124) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_50, c_759])).
% 3.26/1.49  tff(c_770, plain, (![B_212, A_213]: (k5_relat_1(k1_xboole_0, B_212)=k5_relat_1(A_213, k1_xboole_0) | ~v1_relat_1(A_213) | ~v1_relat_1(B_212))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_764])).
% 3.26/1.49  tff(c_774, plain, (![B_212]: (k5_relat_1(k1_xboole_0, k1_xboole_0)=k5_relat_1(k1_xboole_0, B_212) | ~v1_relat_1(B_212))), inference(resolution, [status(thm)], [c_91, c_770])).
% 3.26/1.49  tff(c_782, plain, (![B_214]: (k5_relat_1(k1_xboole_0, B_214)=k1_xboole_0 | ~v1_relat_1(B_214))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_774])).
% 3.26/1.49  tff(c_791, plain, (k5_relat_1(k1_xboole_0, '#skF_7')=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_782])).
% 3.26/1.49  tff(c_798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_791])).
% 3.26/1.49  tff(c_799, plain, (k5_relat_1('#skF_7', k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_60])).
% 3.26/1.49  tff(c_899, plain, (![A_232, B_233]: (r1_tarski(k2_relat_1(k5_relat_1(A_232, B_233)), k2_relat_1(B_233)) | ~v1_relat_1(B_233) | ~v1_relat_1(A_232))), inference(cnfTransformation, [status(thm)], [f_98])).
% 3.26/1.49  tff(c_907, plain, (![A_232]: (r1_tarski(k2_relat_1(k5_relat_1(A_232, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_232))), inference(superposition, [status(thm), theory('equality')], [c_56, c_899])).
% 3.26/1.49  tff(c_913, plain, (![A_234]: (r1_tarski(k2_relat_1(k5_relat_1(A_234, k1_xboole_0)), k1_xboole_0) | ~v1_relat_1(A_234))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_907])).
% 3.26/1.49  tff(c_829, plain, (![B_219, A_220]: (B_219=A_220 | ~r1_tarski(B_219, A_220) | ~r1_tarski(A_220, B_219))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.26/1.49  tff(c_838, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(resolution, [status(thm)], [c_12, c_829])).
% 3.26/1.49  tff(c_923, plain, (![A_235]: (k2_relat_1(k5_relat_1(A_235, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(A_235))), inference(resolution, [status(thm)], [c_913, c_838])).
% 3.26/1.49  tff(c_938, plain, (![A_235]: (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k5_relat_1(A_235, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_235, k1_xboole_0)) | ~v1_relat_1(A_235))), inference(superposition, [status(thm), theory('equality')], [c_923, c_52])).
% 3.26/1.49  tff(c_958, plain, (![A_240]: (~v1_relat_1(k5_relat_1(A_240, k1_xboole_0)) | v1_xboole_0(k5_relat_1(A_240, k1_xboole_0)) | ~v1_relat_1(A_240))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_938])).
% 3.26/1.49  tff(c_967, plain, (![A_241]: (k5_relat_1(A_241, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k5_relat_1(A_241, k1_xboole_0)) | ~v1_relat_1(A_241))), inference(resolution, [status(thm)], [c_958, c_4])).
% 3.26/1.49  tff(c_971, plain, (![A_123]: (k5_relat_1(A_123, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_123))), inference(resolution, [status(thm)], [c_50, c_967])).
% 3.26/1.49  tff(c_975, plain, (![A_242]: (k5_relat_1(A_242, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_242))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_971])).
% 3.26/1.49  tff(c_984, plain, (k5_relat_1('#skF_7', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_62, c_975])).
% 3.26/1.49  tff(c_990, plain, $false, inference(negUnitSimplification, [status(thm)], [c_799, c_984])).
% 3.26/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.26/1.49  
% 3.26/1.49  Inference rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Ref     : 0
% 3.26/1.49  #Sup     : 197
% 3.26/1.49  #Fact    : 0
% 3.26/1.49  #Define  : 0
% 3.26/1.49  #Split   : 1
% 3.26/1.49  #Chain   : 0
% 3.26/1.49  #Close   : 0
% 3.26/1.49  
% 3.26/1.49  Ordering : KBO
% 3.26/1.49  
% 3.26/1.49  Simplification rules
% 3.26/1.49  ----------------------
% 3.26/1.49  #Subsume      : 42
% 3.26/1.49  #Demod        : 204
% 3.26/1.49  #Tautology    : 93
% 3.26/1.49  #SimpNegUnit  : 8
% 3.26/1.49  #BackRed      : 0
% 3.26/1.49  
% 3.26/1.49  #Partial instantiations: 0
% 3.26/1.49  #Strategies tried      : 1
% 3.26/1.49  
% 3.26/1.49  Timing (in seconds)
% 3.26/1.49  ----------------------
% 3.26/1.49  Preprocessing        : 0.34
% 3.26/1.49  Parsing              : 0.17
% 3.26/1.49  CNF conversion       : 0.03
% 3.26/1.49  Main loop            : 0.37
% 3.26/1.49  Inferencing          : 0.14
% 3.26/1.50  Reduction            : 0.11
% 3.26/1.50  Demodulation         : 0.08
% 3.26/1.50  BG Simplification    : 0.02
% 3.26/1.50  Subsumption          : 0.07
% 3.26/1.50  Abstraction          : 0.02
% 3.26/1.50  MUC search           : 0.00
% 3.26/1.50  Cooper               : 0.00
% 3.26/1.50  Total                : 0.74
% 3.26/1.50  Index Insertion      : 0.00
% 3.26/1.50  Index Deletion       : 0.00
% 3.26/1.50  Index Matching       : 0.00
% 3.26/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
