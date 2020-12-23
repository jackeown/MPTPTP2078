%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:37 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.54s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 117 expanded)
%              Number of leaves         :   37 (  53 expanded)
%              Depth                    :    8
%              Number of atoms          :   97 ( 141 expanded)
%              Number of equality atoms :   47 (  73 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_30,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_323,plain,(
    ! [A_88,B_89] : k4_xboole_0(A_88,k4_xboole_0(A_88,B_89)) = k3_xboole_0(A_88,B_89) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_36,plain,(
    ! [A_21] : k4_xboole_0(k1_xboole_0,A_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_371,plain,(
    ! [B_90] : k3_xboole_0(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_323,c_36])).

tff(c_414,plain,(
    ! [B_94] : k3_xboole_0(B_94,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_371])).

tff(c_26,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_422,plain,(
    ! [B_94] : k5_xboole_0(B_94,k1_xboole_0) = k4_xboole_0(B_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_26])).

tff(c_444,plain,(
    ! [B_94] : k5_xboole_0(B_94,k1_xboole_0) = B_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_422])).

tff(c_118,plain,(
    ! [A_46,B_47] : r1_tarski(k4_xboole_0(A_46,B_47),A_46) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [A_15] : r1_tarski(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_118])).

tff(c_206,plain,(
    ! [A_75,B_76] :
      ( k4_xboole_0(A_75,B_76) = k1_xboole_0
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_217,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_121,c_206])).

tff(c_74,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(k1_tarski(A_41),B_42)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_197,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(A_73,B_74) = A_73
      | ~ r1_xboole_0(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5597,plain,(
    ! [A_242,B_243] :
      ( k4_xboole_0(k1_tarski(A_242),B_243) = k1_tarski(A_242)
      | r2_hidden(A_242,B_243) ) ),
    inference(resolution,[status(thm)],[c_74,c_197])).

tff(c_32,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5663,plain,(
    ! [A_242,B_243] :
      ( k4_xboole_0(k1_tarski(A_242),k1_tarski(A_242)) = k3_xboole_0(k1_tarski(A_242),B_243)
      | r2_hidden(A_242,B_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5597,c_32])).

tff(c_5731,plain,(
    ! [A_244,B_245] :
      ( k3_xboole_0(k1_tarski(A_244),B_245) = k1_xboole_0
      | r2_hidden(A_244,B_245) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_5663])).

tff(c_308,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_320,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_308])).

tff(c_5817,plain,(
    ! [B_245,A_244] :
      ( k4_xboole_0(B_245,k1_tarski(A_244)) = k5_xboole_0(B_245,k1_xboole_0)
      | r2_hidden(A_244,B_245) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5731,c_320])).

tff(c_5944,plain,(
    ! [B_246,A_247] :
      ( k4_xboole_0(B_246,k1_tarski(A_247)) = B_246
      | r2_hidden(A_247,B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_444,c_5817])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_190,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_6039,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5944,c_190])).

tff(c_6100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_6039])).

tff(c_6101,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_66,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_167,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [E_30,B_25,C_26] : r2_hidden(E_30,k1_enumset1(E_30,B_25,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_185,plain,(
    ! [A_68,B_69] : r2_hidden(A_68,k2_tarski(A_68,B_69)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_48])).

tff(c_188,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_185])).

tff(c_6102,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6103,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_6113,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6102,c_6103])).

tff(c_6114,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_6244,plain,(
    ! [D_258,B_259,A_260] :
      ( ~ r2_hidden(D_258,B_259)
      | ~ r2_hidden(D_258,k4_xboole_0(A_260,B_259)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6284,plain,(
    ! [D_268] :
      ( ~ r2_hidden(D_268,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_268,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6114,c_6244])).

tff(c_6288,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_188,c_6284])).

tff(c_6292,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6101,c_6288])).

tff(c_6293,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_6336,plain,(
    ! [A_286,B_287] : k1_enumset1(A_286,A_286,B_287) = k2_tarski(A_286,B_287) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [E_30,A_24,B_25] : r2_hidden(E_30,k1_enumset1(A_24,B_25,E_30)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6354,plain,(
    ! [B_288,A_289] : r2_hidden(B_288,k2_tarski(A_289,B_288)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6336,c_44])).

tff(c_6357,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6354])).

tff(c_6294,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_82,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_6413,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6294,c_82])).

tff(c_6876,plain,(
    ! [D_321,B_322,A_323] :
      ( ~ r2_hidden(D_321,B_322)
      | ~ r2_hidden(D_321,k4_xboole_0(A_323,B_322)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6902,plain,(
    ! [D_326] :
      ( ~ r2_hidden(D_326,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_326,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6413,c_6876])).

tff(c_6906,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_6357,c_6902])).

tff(c_6910,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6293,c_6906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n016.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 10:28:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/2.17  
% 5.20/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.53/2.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.53/2.17  
% 5.53/2.17  %Foreground sorts:
% 5.53/2.17  
% 5.53/2.17  
% 5.53/2.17  %Background operators:
% 5.53/2.17  
% 5.53/2.17  
% 5.53/2.17  %Foreground operators:
% 5.53/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.53/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.53/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.53/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.53/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.53/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.53/2.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.53/2.17  tff('#skF_7', type, '#skF_7': $i).
% 5.53/2.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.53/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.53/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.53/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.53/2.17  tff('#skF_5', type, '#skF_5': $i).
% 5.53/2.17  tff('#skF_6', type, '#skF_6': $i).
% 5.53/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.53/2.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.53/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.53/2.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.53/2.17  tff('#skF_8', type, '#skF_8': $i).
% 5.53/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.53/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.53/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.53/2.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.53/2.17  
% 5.54/2.19  tff(f_91, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.54/2.19  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 5.54/2.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.54/2.19  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.54/2.19  tff(f_53, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 5.54/2.19  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.54/2.19  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.54/2.19  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.54/2.19  tff(f_85, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 5.54/2.19  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 5.54/2.19  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.54/2.19  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.54/2.19  tff(f_72, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.54/2.19  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.54/2.19  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.54/2.19  tff(c_126, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_78])).
% 5.54/2.19  tff(c_30, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.54/2.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.54/2.19  tff(c_323, plain, (![A_88, B_89]: (k4_xboole_0(A_88, k4_xboole_0(A_88, B_89))=k3_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.54/2.19  tff(c_36, plain, (![A_21]: (k4_xboole_0(k1_xboole_0, A_21)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.54/2.19  tff(c_371, plain, (![B_90]: (k3_xboole_0(k1_xboole_0, B_90)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_323, c_36])).
% 5.54/2.19  tff(c_414, plain, (![B_94]: (k3_xboole_0(B_94, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_371])).
% 5.54/2.19  tff(c_26, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.54/2.19  tff(c_422, plain, (![B_94]: (k5_xboole_0(B_94, k1_xboole_0)=k4_xboole_0(B_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_414, c_26])).
% 5.54/2.19  tff(c_444, plain, (![B_94]: (k5_xboole_0(B_94, k1_xboole_0)=B_94)), inference(demodulation, [status(thm), theory('equality')], [c_30, c_422])).
% 5.54/2.19  tff(c_118, plain, (![A_46, B_47]: (r1_tarski(k4_xboole_0(A_46, B_47), A_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.54/2.19  tff(c_121, plain, (![A_15]: (r1_tarski(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_30, c_118])).
% 5.54/2.19  tff(c_206, plain, (![A_75, B_76]: (k4_xboole_0(A_75, B_76)=k1_xboole_0 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.54/2.19  tff(c_217, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_121, c_206])).
% 5.54/2.19  tff(c_74, plain, (![A_41, B_42]: (r1_xboole_0(k1_tarski(A_41), B_42) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.54/2.19  tff(c_197, plain, (![A_73, B_74]: (k4_xboole_0(A_73, B_74)=A_73 | ~r1_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.54/2.19  tff(c_5597, plain, (![A_242, B_243]: (k4_xboole_0(k1_tarski(A_242), B_243)=k1_tarski(A_242) | r2_hidden(A_242, B_243))), inference(resolution, [status(thm)], [c_74, c_197])).
% 5.54/2.19  tff(c_32, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.54/2.19  tff(c_5663, plain, (![A_242, B_243]: (k4_xboole_0(k1_tarski(A_242), k1_tarski(A_242))=k3_xboole_0(k1_tarski(A_242), B_243) | r2_hidden(A_242, B_243))), inference(superposition, [status(thm), theory('equality')], [c_5597, c_32])).
% 5.54/2.19  tff(c_5731, plain, (![A_244, B_245]: (k3_xboole_0(k1_tarski(A_244), B_245)=k1_xboole_0 | r2_hidden(A_244, B_245))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_5663])).
% 5.54/2.19  tff(c_308, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.54/2.19  tff(c_320, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_308])).
% 5.54/2.19  tff(c_5817, plain, (![B_245, A_244]: (k4_xboole_0(B_245, k1_tarski(A_244))=k5_xboole_0(B_245, k1_xboole_0) | r2_hidden(A_244, B_245))), inference(superposition, [status(thm), theory('equality')], [c_5731, c_320])).
% 5.54/2.19  tff(c_5944, plain, (![B_246, A_247]: (k4_xboole_0(B_246, k1_tarski(A_247))=B_246 | r2_hidden(A_247, B_246))), inference(demodulation, [status(thm), theory('equality')], [c_444, c_5817])).
% 5.54/2.19  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.54/2.19  tff(c_190, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_76])).
% 5.54/2.19  tff(c_6039, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5944, c_190])).
% 5.54/2.19  tff(c_6100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_6039])).
% 5.54/2.19  tff(c_6101, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_76])).
% 5.54/2.19  tff(c_66, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.54/2.19  tff(c_167, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.54/2.19  tff(c_48, plain, (![E_30, B_25, C_26]: (r2_hidden(E_30, k1_enumset1(E_30, B_25, C_26)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.54/2.19  tff(c_185, plain, (![A_68, B_69]: (r2_hidden(A_68, k2_tarski(A_68, B_69)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_48])).
% 5.54/2.19  tff(c_188, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_185])).
% 5.54/2.19  tff(c_6102, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_76])).
% 5.54/2.19  tff(c_80, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.54/2.19  tff(c_6103, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_80])).
% 5.54/2.19  tff(c_6113, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6102, c_6103])).
% 5.54/2.19  tff(c_6114, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 5.54/2.19  tff(c_6244, plain, (![D_258, B_259, A_260]: (~r2_hidden(D_258, B_259) | ~r2_hidden(D_258, k4_xboole_0(A_260, B_259)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.19  tff(c_6284, plain, (![D_268]: (~r2_hidden(D_268, k1_tarski('#skF_8')) | ~r2_hidden(D_268, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6114, c_6244])).
% 5.54/2.19  tff(c_6288, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_188, c_6284])).
% 5.54/2.19  tff(c_6292, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6101, c_6288])).
% 5.54/2.19  tff(c_6293, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_78])).
% 5.54/2.19  tff(c_6336, plain, (![A_286, B_287]: (k1_enumset1(A_286, A_286, B_287)=k2_tarski(A_286, B_287))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.54/2.19  tff(c_44, plain, (![E_30, A_24, B_25]: (r2_hidden(E_30, k1_enumset1(A_24, B_25, E_30)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.54/2.19  tff(c_6354, plain, (![B_288, A_289]: (r2_hidden(B_288, k2_tarski(A_289, B_288)))), inference(superposition, [status(thm), theory('equality')], [c_6336, c_44])).
% 5.54/2.19  tff(c_6357, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6354])).
% 5.54/2.19  tff(c_6294, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_78])).
% 5.54/2.19  tff(c_82, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_91])).
% 5.54/2.19  tff(c_6413, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_6294, c_82])).
% 5.54/2.19  tff(c_6876, plain, (![D_321, B_322, A_323]: (~r2_hidden(D_321, B_322) | ~r2_hidden(D_321, k4_xboole_0(A_323, B_322)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.54/2.19  tff(c_6902, plain, (![D_326]: (~r2_hidden(D_326, k1_tarski('#skF_8')) | ~r2_hidden(D_326, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6413, c_6876])).
% 5.54/2.19  tff(c_6906, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_6357, c_6902])).
% 5.54/2.19  tff(c_6910, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6293, c_6906])).
% 5.54/2.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.54/2.19  
% 5.54/2.19  Inference rules
% 5.54/2.19  ----------------------
% 5.54/2.19  #Ref     : 0
% 5.54/2.19  #Sup     : 1684
% 5.54/2.19  #Fact    : 0
% 5.54/2.19  #Define  : 0
% 5.54/2.19  #Split   : 3
% 5.54/2.19  #Chain   : 0
% 5.54/2.19  #Close   : 0
% 5.54/2.19  
% 5.54/2.19  Ordering : KBO
% 5.54/2.19  
% 5.54/2.19  Simplification rules
% 5.54/2.19  ----------------------
% 5.54/2.19  #Subsume      : 92
% 5.54/2.19  #Demod        : 1745
% 5.54/2.19  #Tautology    : 1192
% 5.54/2.19  #SimpNegUnit  : 1
% 5.54/2.19  #BackRed      : 3
% 5.54/2.19  
% 5.54/2.19  #Partial instantiations: 0
% 5.54/2.19  #Strategies tried      : 1
% 5.54/2.19  
% 5.54/2.19  Timing (in seconds)
% 5.54/2.19  ----------------------
% 5.54/2.19  Preprocessing        : 0.42
% 5.54/2.19  Parsing              : 0.22
% 5.54/2.19  CNF conversion       : 0.03
% 5.54/2.19  Main loop            : 0.96
% 5.54/2.19  Inferencing          : 0.29
% 5.54/2.19  Reduction            : 0.43
% 5.54/2.19  Demodulation         : 0.36
% 5.54/2.19  BG Simplification    : 0.04
% 5.54/2.19  Subsumption          : 0.15
% 5.54/2.19  Abstraction          : 0.05
% 5.54/2.19  MUC search           : 0.00
% 5.54/2.19  Cooper               : 0.00
% 5.54/2.19  Total                : 1.41
% 5.54/2.19  Index Insertion      : 0.00
% 5.54/2.19  Index Deletion       : 0.00
% 5.54/2.19  Index Matching       : 0.00
% 5.54/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
