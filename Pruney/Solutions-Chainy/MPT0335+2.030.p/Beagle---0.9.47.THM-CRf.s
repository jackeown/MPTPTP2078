%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 25.10s
% Output     : CNFRefutation 25.14s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 262 expanded)
%              Number of leaves         :   34 ( 103 expanded)
%              Depth                    :   18
%              Number of atoms          :  108 ( 410 expanded)
%              Number of equality atoms :   44 ( 149 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_94,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_73,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_58,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_172,plain,(
    ! [A_54,B_55] :
      ( r2_hidden(A_54,B_55)
      | ~ r1_tarski(k1_tarski(A_54),B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_184,plain,(
    ! [A_54,B_26] : r2_hidden(A_54,k2_xboole_0(k1_tarski(A_54),B_26)) ),
    inference(resolution,[status(thm)],[c_40,c_172])).

tff(c_34,plain,(
    ! [A_19,B_20] : r1_tarski(k3_xboole_0(A_19,B_20),A_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_197,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_224,plain,(
    ! [A_19,B_20] : k4_xboole_0(k3_xboole_0(A_19,B_20),A_19) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_34,c_197])).

tff(c_451,plain,(
    ! [D_83,B_84,A_85] :
      ( ~ r2_hidden(D_83,B_84)
      | ~ r2_hidden(D_83,k4_xboole_0(A_85,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_514,plain,(
    ! [D_87,A_88] :
      ( ~ r2_hidden(D_87,A_88)
      | ~ r2_hidden(D_87,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_451])).

tff(c_533,plain,(
    ! [A_89] : ~ r2_hidden(A_89,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_184,c_514])).

tff(c_555,plain,(
    ! [A_92] : r1_xboole_0(A_92,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_533])).

tff(c_42,plain,(
    ! [A_27,B_28] :
      ( k4_xboole_0(A_27,B_28) = A_27
      | ~ r1_xboole_0(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_559,plain,(
    ! [A_92] : k4_xboole_0(A_92,k1_xboole_0) = A_92 ),
    inference(resolution,[status(thm)],[c_555,c_42])).

tff(c_64,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_225,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_197])).

tff(c_377,plain,(
    ! [A_81,B_82] : k4_xboole_0(A_81,k4_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_419,plain,(
    k4_xboole_0('#skF_4',k1_xboole_0) = k3_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_377])).

tff(c_576,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_419])).

tff(c_62,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_859,plain,(
    ! [A_106,B_107,C_108] : k3_xboole_0(k3_xboole_0(A_106,B_107),C_108) = k3_xboole_0(A_106,k3_xboole_0(B_107,C_108)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6070,plain,(
    ! [B_240,A_241,B_242] : k3_xboole_0(B_240,k3_xboole_0(A_241,B_242)) = k3_xboole_0(A_241,k3_xboole_0(B_242,B_240)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_859])).

tff(c_6884,plain,(
    ! [A_248] : k3_xboole_0(A_248,k1_tarski('#skF_7')) = k3_xboole_0('#skF_6',k3_xboole_0(A_248,'#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_6070])).

tff(c_7133,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_6','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_576,c_6884])).

tff(c_7202,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_7')) = k3_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_7133])).

tff(c_60,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_38,plain,(
    ! [A_23,B_24] : k4_xboole_0(A_23,k4_xboole_0(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1145,plain,(
    ! [D_112,A_113,B_114] :
      ( r2_hidden(D_112,k4_xboole_0(A_113,B_114))
      | r2_hidden(D_112,B_114)
      | ~ r2_hidden(D_112,A_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_15374,plain,(
    ! [D_354,A_355,B_356] :
      ( r2_hidden(D_354,k3_xboole_0(A_355,B_356))
      | r2_hidden(D_354,k4_xboole_0(A_355,B_356))
      | ~ r2_hidden(D_354,A_355) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1145])).

tff(c_36,plain,(
    ! [A_21,B_22] : k4_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k4_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_7283,plain,(
    k4_xboole_0('#skF_4',k3_xboole_0('#skF_4','#skF_6')) = k4_xboole_0('#skF_4',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7202,c_36])).

tff(c_7319,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_7')) = k4_xboole_0('#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_7283])).

tff(c_529,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_184,c_514])).

tff(c_226,plain,(
    ! [A_64,B_65] :
      ( r1_tarski(A_64,B_65)
      | k4_xboole_0(A_64,B_65) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_54,plain,(
    ! [A_39,B_40] :
      ( r2_hidden(A_39,B_40)
      | ~ r1_tarski(k1_tarski(A_39),B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2166,plain,(
    ! [A_152,B_153] :
      ( r2_hidden(A_152,B_153)
      | k4_xboole_0(k1_tarski(A_152),B_153) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_226,c_54])).

tff(c_2174,plain,(
    ! [A_152] :
      ( r2_hidden(A_152,k1_xboole_0)
      | k1_tarski(A_152) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_559,c_2166])).

tff(c_2195,plain,(
    ! [A_152] : k1_tarski(A_152) != k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_529,c_2174])).

tff(c_56,plain,(
    ! [A_39,B_40] :
      ( r1_tarski(k1_tarski(A_39),B_40)
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_219,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_xboole_0
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_56,c_197])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_10645,plain,(
    ! [A_308,A_309,B_310] :
      ( ~ r2_hidden('#skF_3'(A_308,k4_xboole_0(A_309,B_310)),B_310)
      | r1_xboole_0(A_308,k4_xboole_0(A_309,B_310)) ) ),
    inference(resolution,[status(thm)],[c_24,c_451])).

tff(c_10797,plain,(
    ! [A_311,A_312] : r1_xboole_0(A_311,k4_xboole_0(A_312,A_311)) ),
    inference(resolution,[status(thm)],[c_26,c_10645])).

tff(c_10931,plain,(
    ! [A_313,A_314] : k4_xboole_0(A_313,k4_xboole_0(A_314,A_313)) = A_313 ),
    inference(resolution,[status(thm)],[c_10797,c_42])).

tff(c_11128,plain,(
    ! [A_39,A_314] :
      ( k1_tarski(A_39) = k1_xboole_0
      | ~ r2_hidden(A_39,k4_xboole_0(A_314,k1_tarski(A_39))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_10931])).

tff(c_11407,plain,(
    ! [A_317,A_318] : ~ r2_hidden(A_317,k4_xboole_0(A_318,k1_tarski(A_317))) ),
    inference(negUnitSimplification,[status(thm)],[c_2195,c_11128])).

tff(c_11425,plain,(
    ~ r2_hidden('#skF_7',k4_xboole_0('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7319,c_11407])).

tff(c_15381,plain,
    ( r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_6'))
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(resolution,[status(thm)],[c_15374,c_11425])).

tff(c_15544,plain,(
    r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_15381])).

tff(c_2379,plain,(
    ! [A_162,B_163] :
      ( k4_xboole_0(k1_tarski(A_162),B_163) = k1_xboole_0
      | ~ r2_hidden(A_162,B_163) ) ),
    inference(resolution,[status(thm)],[c_56,c_197])).

tff(c_327,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_342,plain,(
    ! [A_1,B_2] : k4_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_327])).

tff(c_103459,plain,(
    ! [A_873,B_874] :
      ( k4_xboole_0(k1_tarski(A_873),B_874) = k1_xboole_0
      | ~ r2_hidden(A_873,k3_xboole_0(B_874,k1_tarski(A_873))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2379,c_342])).

tff(c_103526,plain,
    ( k4_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k1_xboole_0
    | ~ r2_hidden('#skF_7',k3_xboole_0('#skF_4','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7202,c_103459])).

tff(c_103589,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_15544,c_103526])).

tff(c_103869,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_xboole_0) = k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_103589,c_38])).

tff(c_103979,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7202,c_559,c_2,c_103869])).

tff(c_103981,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_103979])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:31:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 25.10/17.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.14/17.68  
% 25.14/17.68  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.14/17.68  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 25.14/17.68  
% 25.14/17.68  %Foreground sorts:
% 25.14/17.68  
% 25.14/17.68  
% 25.14/17.68  %Background operators:
% 25.14/17.68  
% 25.14/17.68  
% 25.14/17.68  %Foreground operators:
% 25.14/17.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 25.14/17.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 25.14/17.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 25.14/17.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 25.14/17.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 25.14/17.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 25.14/17.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 25.14/17.68  tff('#skF_7', type, '#skF_7': $i).
% 25.14/17.68  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 25.14/17.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 25.14/17.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 25.14/17.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 25.14/17.68  tff('#skF_5', type, '#skF_5': $i).
% 25.14/17.68  tff('#skF_6', type, '#skF_6': $i).
% 25.14/17.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 25.14/17.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 25.14/17.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 25.14/17.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 25.14/17.68  tff('#skF_4', type, '#skF_4': $i).
% 25.14/17.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 25.14/17.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 25.14/17.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 25.14/17.68  
% 25.14/17.70  tff(f_94, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 25.14/17.70  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 25.14/17.70  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 25.14/17.70  tff(f_69, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 25.14/17.70  tff(f_85, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 25.14/17.70  tff(f_63, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 25.14/17.70  tff(f_59, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 25.14/17.70  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 25.14/17.70  tff(f_73, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 25.14/17.70  tff(f_67, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 25.14/17.70  tff(f_61, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 25.14/17.70  tff(f_65, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 25.14/17.70  tff(c_58, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 25.14/17.70  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 25.14/17.70  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.14/17.70  tff(c_40, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 25.14/17.70  tff(c_172, plain, (![A_54, B_55]: (r2_hidden(A_54, B_55) | ~r1_tarski(k1_tarski(A_54), B_55))), inference(cnfTransformation, [status(thm)], [f_85])).
% 25.14/17.70  tff(c_184, plain, (![A_54, B_26]: (r2_hidden(A_54, k2_xboole_0(k1_tarski(A_54), B_26)))), inference(resolution, [status(thm)], [c_40, c_172])).
% 25.14/17.70  tff(c_34, plain, (![A_19, B_20]: (r1_tarski(k3_xboole_0(A_19, B_20), A_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 25.14/17.70  tff(c_197, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.14/17.70  tff(c_224, plain, (![A_19, B_20]: (k4_xboole_0(k3_xboole_0(A_19, B_20), A_19)=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_197])).
% 25.14/17.70  tff(c_451, plain, (![D_83, B_84, A_85]: (~r2_hidden(D_83, B_84) | ~r2_hidden(D_83, k4_xboole_0(A_85, B_84)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.14/17.70  tff(c_514, plain, (![D_87, A_88]: (~r2_hidden(D_87, A_88) | ~r2_hidden(D_87, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_451])).
% 25.14/17.70  tff(c_533, plain, (![A_89]: (~r2_hidden(A_89, k1_xboole_0))), inference(resolution, [status(thm)], [c_184, c_514])).
% 25.14/17.70  tff(c_555, plain, (![A_92]: (r1_xboole_0(A_92, k1_xboole_0))), inference(resolution, [status(thm)], [c_24, c_533])).
% 25.14/17.70  tff(c_42, plain, (![A_27, B_28]: (k4_xboole_0(A_27, B_28)=A_27 | ~r1_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_73])).
% 25.14/17.70  tff(c_559, plain, (![A_92]: (k4_xboole_0(A_92, k1_xboole_0)=A_92)), inference(resolution, [status(thm)], [c_555, c_42])).
% 25.14/17.70  tff(c_64, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_94])).
% 25.14/17.70  tff(c_225, plain, (k4_xboole_0('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_197])).
% 25.14/17.70  tff(c_377, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k4_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.14/17.70  tff(c_419, plain, (k4_xboole_0('#skF_4', k1_xboole_0)=k3_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_225, c_377])).
% 25.14/17.70  tff(c_576, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_559, c_419])).
% 25.14/17.70  tff(c_62, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_94])).
% 25.14/17.70  tff(c_859, plain, (![A_106, B_107, C_108]: (k3_xboole_0(k3_xboole_0(A_106, B_107), C_108)=k3_xboole_0(A_106, k3_xboole_0(B_107, C_108)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 25.14/17.70  tff(c_6070, plain, (![B_240, A_241, B_242]: (k3_xboole_0(B_240, k3_xboole_0(A_241, B_242))=k3_xboole_0(A_241, k3_xboole_0(B_242, B_240)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_859])).
% 25.14/17.70  tff(c_6884, plain, (![A_248]: (k3_xboole_0(A_248, k1_tarski('#skF_7'))=k3_xboole_0('#skF_6', k3_xboole_0(A_248, '#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_62, c_6070])).
% 25.14/17.70  tff(c_7133, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_6', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_576, c_6884])).
% 25.14/17.70  tff(c_7202, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_7'))=k3_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_7133])).
% 25.14/17.70  tff(c_60, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_94])).
% 25.14/17.70  tff(c_38, plain, (![A_23, B_24]: (k4_xboole_0(A_23, k4_xboole_0(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 25.14/17.70  tff(c_1145, plain, (![D_112, A_113, B_114]: (r2_hidden(D_112, k4_xboole_0(A_113, B_114)) | r2_hidden(D_112, B_114) | ~r2_hidden(D_112, A_113))), inference(cnfTransformation, [status(thm)], [f_37])).
% 25.14/17.70  tff(c_15374, plain, (![D_354, A_355, B_356]: (r2_hidden(D_354, k3_xboole_0(A_355, B_356)) | r2_hidden(D_354, k4_xboole_0(A_355, B_356)) | ~r2_hidden(D_354, A_355))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1145])).
% 25.14/17.70  tff(c_36, plain, (![A_21, B_22]: (k4_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k4_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_65])).
% 25.14/17.70  tff(c_7283, plain, (k4_xboole_0('#skF_4', k3_xboole_0('#skF_4', '#skF_6'))=k4_xboole_0('#skF_4', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_7202, c_36])).
% 25.14/17.70  tff(c_7319, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_7'))=k4_xboole_0('#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_7283])).
% 25.14/17.70  tff(c_529, plain, (![A_54]: (~r2_hidden(A_54, k1_xboole_0))), inference(resolution, [status(thm)], [c_184, c_514])).
% 25.14/17.70  tff(c_226, plain, (![A_64, B_65]: (r1_tarski(A_64, B_65) | k4_xboole_0(A_64, B_65)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 25.14/17.70  tff(c_54, plain, (![A_39, B_40]: (r2_hidden(A_39, B_40) | ~r1_tarski(k1_tarski(A_39), B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 25.14/17.70  tff(c_2166, plain, (![A_152, B_153]: (r2_hidden(A_152, B_153) | k4_xboole_0(k1_tarski(A_152), B_153)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_226, c_54])).
% 25.14/17.70  tff(c_2174, plain, (![A_152]: (r2_hidden(A_152, k1_xboole_0) | k1_tarski(A_152)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_559, c_2166])).
% 25.14/17.70  tff(c_2195, plain, (![A_152]: (k1_tarski(A_152)!=k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_529, c_2174])).
% 25.14/17.70  tff(c_56, plain, (![A_39, B_40]: (r1_tarski(k1_tarski(A_39), B_40) | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_85])).
% 25.14/17.70  tff(c_219, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_xboole_0 | ~r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_56, c_197])).
% 25.14/17.70  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 25.14/17.70  tff(c_10645, plain, (![A_308, A_309, B_310]: (~r2_hidden('#skF_3'(A_308, k4_xboole_0(A_309, B_310)), B_310) | r1_xboole_0(A_308, k4_xboole_0(A_309, B_310)))), inference(resolution, [status(thm)], [c_24, c_451])).
% 25.14/17.70  tff(c_10797, plain, (![A_311, A_312]: (r1_xboole_0(A_311, k4_xboole_0(A_312, A_311)))), inference(resolution, [status(thm)], [c_26, c_10645])).
% 25.14/17.70  tff(c_10931, plain, (![A_313, A_314]: (k4_xboole_0(A_313, k4_xboole_0(A_314, A_313))=A_313)), inference(resolution, [status(thm)], [c_10797, c_42])).
% 25.14/17.70  tff(c_11128, plain, (![A_39, A_314]: (k1_tarski(A_39)=k1_xboole_0 | ~r2_hidden(A_39, k4_xboole_0(A_314, k1_tarski(A_39))))), inference(superposition, [status(thm), theory('equality')], [c_219, c_10931])).
% 25.14/17.70  tff(c_11407, plain, (![A_317, A_318]: (~r2_hidden(A_317, k4_xboole_0(A_318, k1_tarski(A_317))))), inference(negUnitSimplification, [status(thm)], [c_2195, c_11128])).
% 25.14/17.70  tff(c_11425, plain, (~r2_hidden('#skF_7', k4_xboole_0('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7319, c_11407])).
% 25.14/17.70  tff(c_15381, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_6')) | ~r2_hidden('#skF_7', '#skF_4')), inference(resolution, [status(thm)], [c_15374, c_11425])).
% 25.14/17.70  tff(c_15544, plain, (r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_15381])).
% 25.14/17.70  tff(c_2379, plain, (![A_162, B_163]: (k4_xboole_0(k1_tarski(A_162), B_163)=k1_xboole_0 | ~r2_hidden(A_162, B_163))), inference(resolution, [status(thm)], [c_56, c_197])).
% 25.14/17.70  tff(c_327, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 25.14/17.70  tff(c_342, plain, (![A_1, B_2]: (k4_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_327])).
% 25.14/17.70  tff(c_103459, plain, (![A_873, B_874]: (k4_xboole_0(k1_tarski(A_873), B_874)=k1_xboole_0 | ~r2_hidden(A_873, k3_xboole_0(B_874, k1_tarski(A_873))))), inference(superposition, [status(thm), theory('equality')], [c_2379, c_342])).
% 25.14/17.70  tff(c_103526, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k1_xboole_0 | ~r2_hidden('#skF_7', k3_xboole_0('#skF_4', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_7202, c_103459])).
% 25.14/17.70  tff(c_103589, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_15544, c_103526])).
% 25.14/17.70  tff(c_103869, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_xboole_0)=k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_103589, c_38])).
% 25.14/17.70  tff(c_103979, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_7202, c_559, c_2, c_103869])).
% 25.14/17.70  tff(c_103981, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_103979])).
% 25.14/17.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 25.14/17.70  
% 25.14/17.70  Inference rules
% 25.14/17.70  ----------------------
% 25.14/17.70  #Ref     : 0
% 25.14/17.70  #Sup     : 26140
% 25.14/17.70  #Fact    : 0
% 25.14/17.70  #Define  : 0
% 25.14/17.70  #Split   : 0
% 25.14/17.70  #Chain   : 0
% 25.14/17.70  #Close   : 0
% 25.14/17.70  
% 25.14/17.70  Ordering : KBO
% 25.14/17.70  
% 25.14/17.70  Simplification rules
% 25.14/17.70  ----------------------
% 25.14/17.70  #Subsume      : 2582
% 25.14/17.70  #Demod        : 33353
% 25.14/17.70  #Tautology    : 16411
% 25.14/17.70  #SimpNegUnit  : 374
% 25.14/17.70  #BackRed      : 6
% 25.14/17.70  
% 25.14/17.70  #Partial instantiations: 0
% 25.14/17.70  #Strategies tried      : 1
% 25.14/17.70  
% 25.14/17.70  Timing (in seconds)
% 25.14/17.70  ----------------------
% 25.14/17.71  Preprocessing        : 0.32
% 25.14/17.71  Parsing              : 0.15
% 25.14/17.71  CNF conversion       : 0.03
% 25.14/17.71  Main loop            : 16.51
% 25.14/17.71  Inferencing          : 1.56
% 25.14/17.71  Reduction            : 11.19
% 25.14/17.71  Demodulation         : 10.13
% 25.14/17.71  BG Simplification    : 0.17
% 25.14/17.71  Subsumption          : 3.06
% 25.14/17.71  Abstraction          : 0.28
% 25.14/17.71  MUC search           : 0.00
% 25.14/17.71  Cooper               : 0.00
% 25.14/17.71  Total                : 16.87
% 25.14/17.71  Index Insertion      : 0.00
% 25.14/17.71  Index Deletion       : 0.00
% 25.14/17.71  Index Matching       : 0.00
% 25.14/17.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
