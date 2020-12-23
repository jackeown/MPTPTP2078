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
% DateTime   : Thu Dec  3 09:52:56 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.30s
% Verified   : 
% Statistics : Number of formulae       :   74 (  93 expanded)
%              Number of leaves         :   34 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   77 ( 116 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_89,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
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

tff(c_62,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_16,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [A_75,B_76] :
      ( r1_xboole_0(k1_tarski(A_75),B_76)
      | r2_hidden(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_296,plain,(
    ! [A_96,B_97] :
      ( k3_xboole_0(k1_tarski(A_96),B_97) = k1_xboole_0
      | r2_hidden(A_96,B_97) ) ),
    inference(resolution,[status(thm)],[c_162,c_4])).

tff(c_14,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k3_xboole_0(A_10,B_11)) = k4_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_305,plain,(
    ! [A_96,B_97] :
      ( k5_xboole_0(k1_tarski(A_96),k1_xboole_0) = k4_xboole_0(k1_tarski(A_96),B_97)
      | r2_hidden(A_96,B_97) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_296,c_14])).

tff(c_578,plain,(
    ! [A_126,B_127] :
      ( k4_xboole_0(k1_tarski(A_126),B_127) = k1_tarski(A_126)
      | r2_hidden(A_126,B_127) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_305])).

tff(c_60,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_123,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_610,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_578,c_123])).

tff(c_632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_121,c_610])).

tff(c_633,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_44,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_710,plain,(
    ! [A_134,B_135] : k1_enumset1(A_134,A_134,B_135) = k2_tarski(A_134,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_22,plain,(
    ! [E_21,A_15,B_16] : r2_hidden(E_21,k1_enumset1(A_15,B_16,E_21)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_728,plain,(
    ! [B_136,A_137] : r2_hidden(B_136,k2_tarski(A_137,B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_710,c_22])).

tff(c_731,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_728])).

tff(c_634,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') != k1_tarski('#skF_4')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_739,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_64])).

tff(c_18,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_749,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_739,c_18])).

tff(c_1116,plain,(
    ! [A_166,B_167,C_168] :
      ( ~ r1_xboole_0(A_166,B_167)
      | ~ r2_hidden(C_168,B_167)
      | ~ r2_hidden(C_168,A_166) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1144,plain,(
    ! [C_169] :
      ( ~ r2_hidden(C_169,'#skF_7')
      | ~ r2_hidden(C_169,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_749,c_1116])).

tff(c_1156,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_731,c_1144])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_1156])).

tff(c_1163,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_1167,plain,(
    ! [A_175,B_176] : k1_enumset1(A_175,A_175,B_176) = k2_tarski(A_175,B_176) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1185,plain,(
    ! [B_177,A_178] : r2_hidden(B_177,k2_tarski(A_178,B_177)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1167,c_22])).

tff(c_1188,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1185])).

tff(c_1164,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_66,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1266,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),'#skF_7') = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1164,c_66])).

tff(c_1276,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),'#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1266,c_18])).

tff(c_1392,plain,(
    ! [A_200,B_201,C_202] :
      ( ~ r1_xboole_0(A_200,B_201)
      | ~ r2_hidden(C_202,B_201)
      | ~ r2_hidden(C_202,A_200) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1411,plain,(
    ! [C_203] :
      ( ~ r2_hidden(C_203,'#skF_7')
      | ~ r2_hidden(C_203,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1276,c_1392])).

tff(c_1423,plain,(
    ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_1188,c_1411])).

tff(c_1429,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1163,c_1423])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:30:20 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  
% 3.16/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.16/1.50  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.16/1.50  
% 3.16/1.50  %Foreground sorts:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Background operators:
% 3.16/1.50  
% 3.16/1.50  
% 3.16/1.50  %Foreground operators:
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.16/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.16/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.16/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_7', type, '#skF_7': $i).
% 3.16/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.50  tff('#skF_5', type, '#skF_5': $i).
% 3.16/1.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_6', type, '#skF_6': $i).
% 3.16/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.16/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.16/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.16/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.16/1.50  
% 3.30/1.52  tff(f_95, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.30/1.52  tff(f_53, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.30/1.52  tff(f_89, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.30/1.52  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.30/1.52  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.30/1.52  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.30/1.52  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.30/1.52  tff(f_70, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.30/1.52  tff(f_55, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.30/1.52  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.30/1.52  tff(c_62, plain, (~r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.30/1.52  tff(c_121, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_62])).
% 3.30/1.52  tff(c_16, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.30/1.52  tff(c_162, plain, (![A_75, B_76]: (r1_xboole_0(k1_tarski(A_75), B_76) | r2_hidden(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.30/1.52  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.30/1.52  tff(c_296, plain, (![A_96, B_97]: (k3_xboole_0(k1_tarski(A_96), B_97)=k1_xboole_0 | r2_hidden(A_96, B_97))), inference(resolution, [status(thm)], [c_162, c_4])).
% 3.30/1.52  tff(c_14, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k3_xboole_0(A_10, B_11))=k4_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.30/1.52  tff(c_305, plain, (![A_96, B_97]: (k5_xboole_0(k1_tarski(A_96), k1_xboole_0)=k4_xboole_0(k1_tarski(A_96), B_97) | r2_hidden(A_96, B_97))), inference(superposition, [status(thm), theory('equality')], [c_296, c_14])).
% 3.30/1.52  tff(c_578, plain, (![A_126, B_127]: (k4_xboole_0(k1_tarski(A_126), B_127)=k1_tarski(A_126) | r2_hidden(A_126, B_127))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_305])).
% 3.30/1.52  tff(c_60, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.30/1.52  tff(c_123, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4')), inference(splitLeft, [status(thm)], [c_60])).
% 3.30/1.52  tff(c_610, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_578, c_123])).
% 3.30/1.52  tff(c_632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_121, c_610])).
% 3.30/1.52  tff(c_633, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_60])).
% 3.30/1.52  tff(c_44, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.30/1.52  tff(c_710, plain, (![A_134, B_135]: (k1_enumset1(A_134, A_134, B_135)=k2_tarski(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.30/1.52  tff(c_22, plain, (![E_21, A_15, B_16]: (r2_hidden(E_21, k1_enumset1(A_15, B_16, E_21)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.30/1.52  tff(c_728, plain, (![B_136, A_137]: (r2_hidden(B_136, k2_tarski(A_137, B_136)))), inference(superposition, [status(thm), theory('equality')], [c_710, c_22])).
% 3.30/1.52  tff(c_731, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_728])).
% 3.30/1.52  tff(c_634, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_60])).
% 3.30/1.52  tff(c_64, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')!=k1_tarski('#skF_4') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.30/1.52  tff(c_739, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_634, c_64])).
% 3.30/1.52  tff(c_18, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.30/1.52  tff(c_749, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_739, c_18])).
% 3.30/1.52  tff(c_1116, plain, (![A_166, B_167, C_168]: (~r1_xboole_0(A_166, B_167) | ~r2_hidden(C_168, B_167) | ~r2_hidden(C_168, A_166))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.52  tff(c_1144, plain, (![C_169]: (~r2_hidden(C_169, '#skF_7') | ~r2_hidden(C_169, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_749, c_1116])).
% 3.30/1.52  tff(c_1156, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_731, c_1144])).
% 3.30/1.52  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_633, c_1156])).
% 3.30/1.52  tff(c_1163, plain, (r2_hidden('#skF_6', '#skF_7')), inference(splitRight, [status(thm)], [c_62])).
% 3.30/1.52  tff(c_1167, plain, (![A_175, B_176]: (k1_enumset1(A_175, A_175, B_176)=k2_tarski(A_175, B_176))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.30/1.52  tff(c_1185, plain, (![B_177, A_178]: (r2_hidden(B_177, k2_tarski(A_178, B_177)))), inference(superposition, [status(thm), theory('equality')], [c_1167, c_22])).
% 3.30/1.52  tff(c_1188, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1185])).
% 3.30/1.52  tff(c_1164, plain, (r2_hidden('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_62])).
% 3.30/1.52  tff(c_66, plain, (~r2_hidden('#skF_4', '#skF_5') | k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.30/1.52  tff(c_1266, plain, (k4_xboole_0(k1_tarski('#skF_6'), '#skF_7')=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1164, c_66])).
% 3.30/1.52  tff(c_1276, plain, (r1_xboole_0(k1_tarski('#skF_6'), '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1266, c_18])).
% 3.30/1.52  tff(c_1392, plain, (![A_200, B_201, C_202]: (~r1_xboole_0(A_200, B_201) | ~r2_hidden(C_202, B_201) | ~r2_hidden(C_202, A_200))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.30/1.52  tff(c_1411, plain, (![C_203]: (~r2_hidden(C_203, '#skF_7') | ~r2_hidden(C_203, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_1276, c_1392])).
% 3.30/1.52  tff(c_1423, plain, (~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_1188, c_1411])).
% 3.30/1.52  tff(c_1429, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1163, c_1423])).
% 3.30/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.30/1.52  
% 3.30/1.52  Inference rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Ref     : 0
% 3.30/1.52  #Sup     : 340
% 3.30/1.52  #Fact    : 0
% 3.30/1.52  #Define  : 0
% 3.30/1.52  #Split   : 2
% 3.30/1.52  #Chain   : 0
% 3.30/1.52  #Close   : 0
% 3.30/1.52  
% 3.30/1.52  Ordering : KBO
% 3.30/1.52  
% 3.30/1.52  Simplification rules
% 3.30/1.52  ----------------------
% 3.30/1.52  #Subsume      : 26
% 3.30/1.52  #Demod        : 128
% 3.30/1.52  #Tautology    : 212
% 3.30/1.52  #SimpNegUnit  : 5
% 3.30/1.52  #BackRed      : 0
% 3.30/1.52  
% 3.30/1.52  #Partial instantiations: 0
% 3.30/1.52  #Strategies tried      : 1
% 3.30/1.52  
% 3.30/1.52  Timing (in seconds)
% 3.30/1.52  ----------------------
% 3.30/1.52  Preprocessing        : 0.33
% 3.30/1.52  Parsing              : 0.17
% 3.30/1.52  CNF conversion       : 0.03
% 3.30/1.52  Main loop            : 0.40
% 3.30/1.52  Inferencing          : 0.14
% 3.30/1.52  Reduction            : 0.13
% 3.30/1.52  Demodulation         : 0.10
% 3.30/1.52  BG Simplification    : 0.02
% 3.30/1.52  Subsumption          : 0.06
% 3.30/1.52  Abstraction          : 0.02
% 3.30/1.52  MUC search           : 0.00
% 3.30/1.52  Cooper               : 0.00
% 3.30/1.52  Total                : 0.76
% 3.30/1.52  Index Insertion      : 0.00
% 3.30/1.52  Index Deletion       : 0.00
% 3.30/1.52  Index Matching       : 0.00
% 3.30/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
