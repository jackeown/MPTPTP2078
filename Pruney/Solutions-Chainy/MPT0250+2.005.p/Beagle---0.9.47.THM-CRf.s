%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:32 EST 2020

% Result     : Theorem 3.53s
% Output     : CNFRefutation 3.53s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 137 expanded)
%              Number of leaves         :   33 (  61 expanded)
%              Depth                    :   11
%              Number of atoms          :   88 ( 210 expanded)
%              Number of equality atoms :   34 (  88 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_99,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_101,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_97,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_82,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_111,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_80,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_116,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_52,axiom,(
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

tff(c_66,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_208,plain,(
    ! [A_77,B_78] : k1_enumset1(A_77,A_77,B_78) = k2_tarski(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_46,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_242,plain,(
    ! [A_81,B_82] : r2_hidden(A_81,k2_tarski(A_81,B_82)) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_46])).

tff(c_251,plain,(
    ! [A_31] : r2_hidden(A_31,k1_tarski(A_31)) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_242])).

tff(c_40,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_165,plain,(
    ! [A_73,B_74] : k3_tarski(k2_tarski(A_73,B_74)) = k2_xboole_0(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_332,plain,(
    ! [B_92,A_93] : k3_tarski(k2_tarski(B_92,A_93)) = k2_xboole_0(A_93,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_78,plain,(
    ! [A_52,B_53] : k3_tarski(k2_tarski(A_52,B_53)) = k2_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_358,plain,(
    ! [B_94,A_95] : k2_xboole_0(B_94,A_95) = k2_xboole_0(A_95,B_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_78])).

tff(c_38,plain,(
    ! [A_20,B_21] : r1_tarski(A_20,k2_xboole_0(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_270,plain,(
    ! [B_86,A_87] : k3_tarski(k2_tarski(B_86,A_87)) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_165])).

tff(c_276,plain,(
    ! [B_86,A_87] : k2_xboole_0(B_86,A_87) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_78])).

tff(c_82,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_226,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_236,plain,
    ( k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_82,c_226])).

tff(c_254,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_236])).

tff(c_297,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_276,c_254])).

tff(c_301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_297])).

tff(c_302,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_236])).

tff(c_373,plain,(
    k2_xboole_0('#skF_5',k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_358,c_302])).

tff(c_32,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_xboole_0(A_15,C_17)
      | ~ r1_xboole_0(A_15,k2_xboole_0(B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_430,plain,(
    ! [A_15] :
      ( r1_xboole_0(A_15,k1_tarski('#skF_4'))
      | ~ r1_xboole_0(A_15,'#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_32])).

tff(c_636,plain,(
    ! [A_124,B_125,C_126] :
      ( ~ r1_xboole_0(A_124,B_125)
      | ~ r2_hidden(C_126,B_125)
      | ~ r2_hidden(C_126,A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1122,plain,(
    ! [C_180,A_181] :
      ( ~ r2_hidden(C_180,k1_tarski('#skF_4'))
      | ~ r2_hidden(C_180,A_181)
      | ~ r1_xboole_0(A_181,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_430,c_636])).

tff(c_1135,plain,(
    ! [A_182] :
      ( ~ r2_hidden('#skF_4',A_182)
      | ~ r1_xboole_0(A_182,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_251,c_1122])).

tff(c_1166,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_251,c_1135])).

tff(c_80,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1417,plain,(
    ! [E_214,C_215,B_216,A_217] :
      ( E_214 = C_215
      | E_214 = B_216
      | E_214 = A_217
      | ~ r2_hidden(E_214,k1_enumset1(A_217,B_216,C_215)) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1540,plain,(
    ! [E_236,B_237,A_238] :
      ( E_236 = B_237
      | E_236 = A_238
      | E_236 = A_238
      | ~ r2_hidden(E_236,k2_tarski(A_238,B_237)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1417])).

tff(c_1570,plain,(
    ! [E_239,A_240] :
      ( E_239 = A_240
      | E_239 = A_240
      | E_239 = A_240
      | ~ r2_hidden(E_239,k1_tarski(A_240)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_1540])).

tff(c_1586,plain,(
    ! [A_241,B_242] :
      ( '#skF_1'(k1_tarski(A_241),B_242) = A_241
      | r1_xboole_0(k1_tarski(A_241),B_242) ) ),
    inference(resolution,[status(thm)],[c_20,c_1570])).

tff(c_1604,plain,(
    '#skF_1'(k1_tarski('#skF_4'),'#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1586,c_1166])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_1'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1666,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1604,c_18])).

tff(c_1672,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1166,c_80,c_1666])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:45:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.53/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.66  
% 3.53/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.67  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.53/1.67  
% 3.53/1.67  %Foreground sorts:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Background operators:
% 3.53/1.67  
% 3.53/1.67  
% 3.53/1.67  %Foreground operators:
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.53/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.53/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.53/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.53/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.53/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.53/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.53/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.53/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.53/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.53/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.53/1.67  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.53/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.53/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.53/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.53/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.53/1.67  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.53/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.53/1.67  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.53/1.67  
% 3.53/1.68  tff(f_99, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.53/1.68  tff(f_101, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.53/1.68  tff(f_97, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.53/1.68  tff(f_82, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.53/1.68  tff(f_111, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.53/1.68  tff(f_80, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.53/1.68  tff(f_116, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.53/1.68  tff(f_58, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.53/1.68  tff(f_76, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 3.53/1.68  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.53/1.68  tff(c_66, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.53/1.68  tff(c_208, plain, (![A_77, B_78]: (k1_enumset1(A_77, A_77, B_78)=k2_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.53/1.68  tff(c_46, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.68  tff(c_242, plain, (![A_81, B_82]: (r2_hidden(A_81, k2_tarski(A_81, B_82)))), inference(superposition, [status(thm), theory('equality')], [c_208, c_46])).
% 3.53/1.68  tff(c_251, plain, (![A_31]: (r2_hidden(A_31, k1_tarski(A_31)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_242])).
% 3.53/1.68  tff(c_40, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.53/1.68  tff(c_165, plain, (![A_73, B_74]: (k3_tarski(k2_tarski(A_73, B_74))=k2_xboole_0(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.53/1.68  tff(c_332, plain, (![B_92, A_93]: (k3_tarski(k2_tarski(B_92, A_93))=k2_xboole_0(A_93, B_92))), inference(superposition, [status(thm), theory('equality')], [c_40, c_165])).
% 3.53/1.68  tff(c_78, plain, (![A_52, B_53]: (k3_tarski(k2_tarski(A_52, B_53))=k2_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_111])).
% 3.53/1.68  tff(c_358, plain, (![B_94, A_95]: (k2_xboole_0(B_94, A_95)=k2_xboole_0(A_95, B_94))), inference(superposition, [status(thm), theory('equality')], [c_332, c_78])).
% 3.53/1.68  tff(c_38, plain, (![A_20, B_21]: (r1_tarski(A_20, k2_xboole_0(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.53/1.68  tff(c_270, plain, (![B_86, A_87]: (k3_tarski(k2_tarski(B_86, A_87))=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_40, c_165])).
% 3.53/1.68  tff(c_276, plain, (![B_86, A_87]: (k2_xboole_0(B_86, A_87)=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_270, c_78])).
% 3.53/1.68  tff(c_82, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.68  tff(c_226, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.53/1.68  tff(c_236, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_82, c_226])).
% 3.53/1.68  tff(c_254, plain, (~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_236])).
% 3.53/1.68  tff(c_297, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_276, c_254])).
% 3.53/1.68  tff(c_301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_297])).
% 3.53/1.68  tff(c_302, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_236])).
% 3.53/1.68  tff(c_373, plain, (k2_xboole_0('#skF_5', k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_358, c_302])).
% 3.53/1.68  tff(c_32, plain, (![A_15, C_17, B_16]: (r1_xboole_0(A_15, C_17) | ~r1_xboole_0(A_15, k2_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.53/1.68  tff(c_430, plain, (![A_15]: (r1_xboole_0(A_15, k1_tarski('#skF_4')) | ~r1_xboole_0(A_15, '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_373, c_32])).
% 3.53/1.68  tff(c_636, plain, (![A_124, B_125, C_126]: (~r1_xboole_0(A_124, B_125) | ~r2_hidden(C_126, B_125) | ~r2_hidden(C_126, A_124))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.68  tff(c_1122, plain, (![C_180, A_181]: (~r2_hidden(C_180, k1_tarski('#skF_4')) | ~r2_hidden(C_180, A_181) | ~r1_xboole_0(A_181, '#skF_5'))), inference(resolution, [status(thm)], [c_430, c_636])).
% 3.53/1.68  tff(c_1135, plain, (![A_182]: (~r2_hidden('#skF_4', A_182) | ~r1_xboole_0(A_182, '#skF_5'))), inference(resolution, [status(thm)], [c_251, c_1122])).
% 3.53/1.68  tff(c_1166, plain, (~r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(resolution, [status(thm)], [c_251, c_1135])).
% 3.53/1.68  tff(c_80, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.53/1.68  tff(c_20, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.68  tff(c_68, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.53/1.68  tff(c_1417, plain, (![E_214, C_215, B_216, A_217]: (E_214=C_215 | E_214=B_216 | E_214=A_217 | ~r2_hidden(E_214, k1_enumset1(A_217, B_216, C_215)))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.53/1.68  tff(c_1540, plain, (![E_236, B_237, A_238]: (E_236=B_237 | E_236=A_238 | E_236=A_238 | ~r2_hidden(E_236, k2_tarski(A_238, B_237)))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1417])).
% 3.53/1.68  tff(c_1570, plain, (![E_239, A_240]: (E_239=A_240 | E_239=A_240 | E_239=A_240 | ~r2_hidden(E_239, k1_tarski(A_240)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_1540])).
% 3.53/1.68  tff(c_1586, plain, (![A_241, B_242]: ('#skF_1'(k1_tarski(A_241), B_242)=A_241 | r1_xboole_0(k1_tarski(A_241), B_242))), inference(resolution, [status(thm)], [c_20, c_1570])).
% 3.53/1.68  tff(c_1604, plain, ('#skF_1'(k1_tarski('#skF_4'), '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_1586, c_1166])).
% 3.53/1.68  tff(c_18, plain, (![A_6, B_7]: (r2_hidden('#skF_1'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.53/1.68  tff(c_1666, plain, (r2_hidden('#skF_4', '#skF_5') | r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1604, c_18])).
% 3.53/1.68  tff(c_1672, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1166, c_80, c_1666])).
% 3.53/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.53/1.68  
% 3.53/1.68  Inference rules
% 3.53/1.68  ----------------------
% 3.53/1.68  #Ref     : 0
% 3.53/1.68  #Sup     : 372
% 3.53/1.68  #Fact    : 0
% 3.53/1.68  #Define  : 0
% 3.53/1.68  #Split   : 2
% 3.53/1.68  #Chain   : 0
% 3.53/1.68  #Close   : 0
% 3.53/1.68  
% 3.53/1.68  Ordering : KBO
% 3.53/1.68  
% 3.53/1.68  Simplification rules
% 3.53/1.68  ----------------------
% 3.53/1.68  #Subsume      : 53
% 3.53/1.68  #Demod        : 121
% 3.53/1.68  #Tautology    : 177
% 3.53/1.68  #SimpNegUnit  : 2
% 3.53/1.68  #BackRed      : 3
% 3.53/1.68  
% 3.53/1.68  #Partial instantiations: 0
% 3.53/1.68  #Strategies tried      : 1
% 3.53/1.68  
% 3.53/1.68  Timing (in seconds)
% 3.53/1.68  ----------------------
% 3.53/1.68  Preprocessing        : 0.33
% 3.53/1.68  Parsing              : 0.16
% 3.53/1.68  CNF conversion       : 0.03
% 3.53/1.68  Main loop            : 0.48
% 3.53/1.68  Inferencing          : 0.16
% 3.53/1.68  Reduction            : 0.18
% 3.53/1.68  Demodulation         : 0.14
% 3.53/1.68  BG Simplification    : 0.02
% 3.53/1.68  Subsumption          : 0.09
% 3.53/1.68  Abstraction          : 0.02
% 3.53/1.68  MUC search           : 0.00
% 3.53/1.68  Cooper               : 0.00
% 3.53/1.68  Total                : 0.84
% 3.53/1.68  Index Insertion      : 0.00
% 3.53/1.68  Index Deletion       : 0.00
% 3.53/1.68  Index Matching       : 0.00
% 3.53/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
