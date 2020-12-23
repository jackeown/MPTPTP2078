%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:06 EST 2020

% Result     : Theorem 11.98s
% Output     : CNFRefutation 11.98s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 108 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :   11
%              Number of atoms          :   90 ( 142 expanded)
%              Number of equality atoms :   37 (  63 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_97,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_69,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_44,plain,(
    r1_xboole_0('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_157,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_189,plain,(
    k3_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_157])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k3_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1715,plain,(
    ! [A_127,B_128,C_129] :
      ( k3_xboole_0(A_127,k2_xboole_0(B_128,C_129)) = k3_xboole_0(A_127,C_129)
      | ~ r1_xboole_0(A_127,B_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_144,plain,(
    ! [A_53,B_54] :
      ( r1_xboole_0(A_53,B_54)
      | k3_xboole_0(A_53,B_54) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_42,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_149,plain,(
    k3_xboole_0(k2_xboole_0('#skF_2','#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_144,c_42])).

tff(c_152,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_2','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_149])).

tff(c_1778,plain,
    ( k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0
    | ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1715,c_152])).

tff(c_1829,plain,(
    ~ r1_xboole_0('#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2,c_1778])).

tff(c_1856,plain,(
    k3_xboole_0('#skF_3','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_1829])).

tff(c_20,plain,(
    ! [A_17] : k4_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_23] : r1_xboole_0(A_23,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_188,plain,(
    ! [A_23] : k3_xboole_0(A_23,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_420,plain,(
    ! [A_71,B_72] : k4_xboole_0(A_71,k4_xboole_0(A_71,B_72)) = k3_xboole_0(A_71,B_72) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_450,plain,(
    ! [A_17] : k4_xboole_0(A_17,A_17) = k3_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_420])).

tff(c_455,plain,(
    ! [A_73] : k4_xboole_0(A_73,A_73) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_450])).

tff(c_22,plain,(
    ! [A_18,B_19] : k4_xboole_0(A_18,k4_xboole_0(A_18,B_19)) = k3_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_460,plain,(
    ! [A_73] : k4_xboole_0(A_73,k1_xboole_0) = k3_xboole_0(A_73,A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_22])).

tff(c_484,plain,(
    ! [A_73] : k3_xboole_0(A_73,A_73) = A_73 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_460])).

tff(c_1282,plain,(
    ! [A_117,B_118,C_119] : k3_xboole_0(k3_xboole_0(A_117,B_118),C_119) = k3_xboole_0(A_117,k3_xboole_0(B_118,C_119)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3234,plain,(
    ! [A_170,B_171,C_172] : k3_xboole_0(k3_xboole_0(A_170,B_171),C_172) = k3_xboole_0(B_171,k3_xboole_0(A_170,C_172)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1282])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k3_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k3_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_25115,plain,(
    ! [B_444,A_445,C_446] : k3_xboole_0(B_444,k3_xboole_0(A_445,C_446)) = k3_xboole_0(A_445,k3_xboole_0(B_444,C_446)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3234,c_18])).

tff(c_33048,plain,(
    ! [A_487,A_488] : k3_xboole_0(A_487,k3_xboole_0(A_488,A_487)) = k3_xboole_0(A_488,A_487) ),
    inference(superposition,[status(thm),theory(equality)],[c_484,c_25115])).

tff(c_48,plain,(
    r1_tarski(k3_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_49,plain,(
    r1_tarski(k3_xboole_0('#skF_3','#skF_2'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_48])).

tff(c_38,plain,(
    ! [A_35,B_36] :
      ( r1_xboole_0(k1_tarski(A_35),B_36)
      | r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1142,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_xboole_0(A_106,C_107)
      | ~ r1_xboole_0(B_108,C_107)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_7068,plain,(
    ! [A_237,B_238,A_239] :
      ( r1_xboole_0(A_237,B_238)
      | ~ r1_tarski(A_237,k1_tarski(A_239))
      | r2_hidden(A_239,B_238) ) ),
    inference(resolution,[status(thm)],[c_38,c_1142])).

tff(c_7298,plain,(
    ! [B_246] :
      ( r1_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_246)
      | r2_hidden('#skF_5',B_246) ) ),
    inference(resolution,[status(thm)],[c_49,c_7068])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_7305,plain,(
    ! [B_246] :
      ( k3_xboole_0(k3_xboole_0('#skF_3','#skF_2'),B_246) = k1_xboole_0
      | r2_hidden('#skF_5',B_246) ) ),
    inference(resolution,[status(thm)],[c_7298,c_4])).

tff(c_7311,plain,(
    ! [B_246] :
      ( k3_xboole_0('#skF_3',k3_xboole_0('#skF_2',B_246)) = k1_xboole_0
      | r2_hidden('#skF_5',B_246) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_7305])).

tff(c_33214,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33048,c_7311])).

tff(c_33771,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | r2_hidden('#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_33214])).

tff(c_33772,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1856,c_33771])).

tff(c_46,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1022,plain,(
    ! [A_98,B_99,C_100] :
      ( ~ r1_xboole_0(A_98,B_99)
      | ~ r2_hidden(C_100,B_99)
      | ~ r2_hidden(C_100,A_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_9100,plain,(
    ! [C_281,B_282,A_283] :
      ( ~ r2_hidden(C_281,B_282)
      | ~ r2_hidden(C_281,A_283)
      | k3_xboole_0(A_283,B_282) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_1022])).

tff(c_9112,plain,(
    ! [A_283] :
      ( ~ r2_hidden('#skF_5',A_283)
      | k3_xboole_0(A_283,'#skF_4') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_46,c_9100])).

tff(c_34364,plain,(
    k3_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_33772,c_9112])).

tff(c_34385,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_2,c_34364])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:14:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 11.98/5.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.98/5.57  
% 11.98/5.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.98/5.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 11.98/5.57  
% 11.98/5.57  %Foreground sorts:
% 11.98/5.57  
% 11.98/5.57  
% 11.98/5.57  %Background operators:
% 11.98/5.57  
% 11.98/5.57  
% 11.98/5.57  %Foreground operators:
% 11.98/5.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 11.98/5.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 11.98/5.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 11.98/5.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 11.98/5.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 11.98/5.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 11.98/5.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 11.98/5.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 11.98/5.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 11.98/5.57  tff('#skF_5', type, '#skF_5': $i).
% 11.98/5.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 11.98/5.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 11.98/5.57  tff('#skF_2', type, '#skF_2': $i).
% 11.98/5.57  tff('#skF_3', type, '#skF_3': $i).
% 11.98/5.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 11.98/5.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 11.98/5.57  tff('#skF_4', type, '#skF_4': $i).
% 11.98/5.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 11.98/5.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 11.98/5.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 11.98/5.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 11.98/5.57  
% 11.98/5.58  tff(f_97, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 11.98/5.58  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 11.98/5.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 11.98/5.58  tff(f_73, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 11.98/5.58  tff(f_59, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 11.98/5.58  tff(f_69, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 11.98/5.58  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 11.98/5.58  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 11.98/5.58  tff(f_86, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 11.98/5.58  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 11.98/5.58  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 11.98/5.58  tff(c_44, plain, (r1_xboole_0('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.98/5.58  tff(c_157, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.98/5.58  tff(c_189, plain, (k3_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_157])).
% 11.98/5.58  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 11.98/5.58  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k3_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.98/5.58  tff(c_1715, plain, (![A_127, B_128, C_129]: (k3_xboole_0(A_127, k2_xboole_0(B_128, C_129))=k3_xboole_0(A_127, C_129) | ~r1_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_73])).
% 11.98/5.58  tff(c_144, plain, (![A_53, B_54]: (r1_xboole_0(A_53, B_54) | k3_xboole_0(A_53, B_54)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.98/5.58  tff(c_42, plain, (~r1_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.98/5.58  tff(c_149, plain, (k3_xboole_0(k2_xboole_0('#skF_2', '#skF_4'), '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_144, c_42])).
% 11.98/5.58  tff(c_152, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_149])).
% 11.98/5.58  tff(c_1778, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0 | ~r1_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1715, c_152])).
% 11.98/5.58  tff(c_1829, plain, (~r1_xboole_0('#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_189, c_2, c_1778])).
% 11.98/5.58  tff(c_1856, plain, (k3_xboole_0('#skF_3', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_1829])).
% 11.98/5.58  tff(c_20, plain, (![A_17]: (k4_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_59])).
% 11.98/5.58  tff(c_26, plain, (![A_23]: (r1_xboole_0(A_23, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_69])).
% 11.98/5.58  tff(c_188, plain, (![A_23]: (k3_xboole_0(A_23, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_157])).
% 11.98/5.58  tff(c_420, plain, (![A_71, B_72]: (k4_xboole_0(A_71, k4_xboole_0(A_71, B_72))=k3_xboole_0(A_71, B_72))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.98/5.58  tff(c_450, plain, (![A_17]: (k4_xboole_0(A_17, A_17)=k3_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_420])).
% 11.98/5.58  tff(c_455, plain, (![A_73]: (k4_xboole_0(A_73, A_73)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_450])).
% 11.98/5.58  tff(c_22, plain, (![A_18, B_19]: (k4_xboole_0(A_18, k4_xboole_0(A_18, B_19))=k3_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_61])).
% 11.98/5.58  tff(c_460, plain, (![A_73]: (k4_xboole_0(A_73, k1_xboole_0)=k3_xboole_0(A_73, A_73))), inference(superposition, [status(thm), theory('equality')], [c_455, c_22])).
% 11.98/5.58  tff(c_484, plain, (![A_73]: (k3_xboole_0(A_73, A_73)=A_73)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_460])).
% 11.98/5.58  tff(c_1282, plain, (![A_117, B_118, C_119]: (k3_xboole_0(k3_xboole_0(A_117, B_118), C_119)=k3_xboole_0(A_117, k3_xboole_0(B_118, C_119)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.98/5.58  tff(c_3234, plain, (![A_170, B_171, C_172]: (k3_xboole_0(k3_xboole_0(A_170, B_171), C_172)=k3_xboole_0(B_171, k3_xboole_0(A_170, C_172)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1282])).
% 11.98/5.58  tff(c_18, plain, (![A_14, B_15, C_16]: (k3_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k3_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 11.98/5.58  tff(c_25115, plain, (![B_444, A_445, C_446]: (k3_xboole_0(B_444, k3_xboole_0(A_445, C_446))=k3_xboole_0(A_445, k3_xboole_0(B_444, C_446)))), inference(superposition, [status(thm), theory('equality')], [c_3234, c_18])).
% 11.98/5.58  tff(c_33048, plain, (![A_487, A_488]: (k3_xboole_0(A_487, k3_xboole_0(A_488, A_487))=k3_xboole_0(A_488, A_487))), inference(superposition, [status(thm), theory('equality')], [c_484, c_25115])).
% 11.98/5.58  tff(c_48, plain, (r1_tarski(k3_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.98/5.58  tff(c_49, plain, (r1_tarski(k3_xboole_0('#skF_3', '#skF_2'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_48])).
% 11.98/5.58  tff(c_38, plain, (![A_35, B_36]: (r1_xboole_0(k1_tarski(A_35), B_36) | r2_hidden(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_86])).
% 11.98/5.58  tff(c_1142, plain, (![A_106, C_107, B_108]: (r1_xboole_0(A_106, C_107) | ~r1_xboole_0(B_108, C_107) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_67])).
% 11.98/5.58  tff(c_7068, plain, (![A_237, B_238, A_239]: (r1_xboole_0(A_237, B_238) | ~r1_tarski(A_237, k1_tarski(A_239)) | r2_hidden(A_239, B_238))), inference(resolution, [status(thm)], [c_38, c_1142])).
% 11.98/5.58  tff(c_7298, plain, (![B_246]: (r1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_246) | r2_hidden('#skF_5', B_246))), inference(resolution, [status(thm)], [c_49, c_7068])).
% 11.98/5.58  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 11.98/5.58  tff(c_7305, plain, (![B_246]: (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_2'), B_246)=k1_xboole_0 | r2_hidden('#skF_5', B_246))), inference(resolution, [status(thm)], [c_7298, c_4])).
% 11.98/5.58  tff(c_7311, plain, (![B_246]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_2', B_246))=k1_xboole_0 | r2_hidden('#skF_5', B_246))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_7305])).
% 11.98/5.58  tff(c_33214, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33048, c_7311])).
% 11.98/5.58  tff(c_33771, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | r2_hidden('#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_33214])).
% 11.98/5.58  tff(c_33772, plain, (r2_hidden('#skF_5', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1856, c_33771])).
% 11.98/5.58  tff(c_46, plain, (r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_97])).
% 11.98/5.58  tff(c_1022, plain, (![A_98, B_99, C_100]: (~r1_xboole_0(A_98, B_99) | ~r2_hidden(C_100, B_99) | ~r2_hidden(C_100, A_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 11.98/5.58  tff(c_9100, plain, (![C_281, B_282, A_283]: (~r2_hidden(C_281, B_282) | ~r2_hidden(C_281, A_283) | k3_xboole_0(A_283, B_282)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_1022])).
% 11.98/5.58  tff(c_9112, plain, (![A_283]: (~r2_hidden('#skF_5', A_283) | k3_xboole_0(A_283, '#skF_4')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_46, c_9100])).
% 11.98/5.58  tff(c_34364, plain, (k3_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_33772, c_9112])).
% 11.98/5.58  tff(c_34385, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_189, c_2, c_34364])).
% 11.98/5.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 11.98/5.58  
% 11.98/5.58  Inference rules
% 11.98/5.58  ----------------------
% 11.98/5.58  #Ref     : 0
% 11.98/5.58  #Sup     : 8456
% 11.98/5.58  #Fact    : 0
% 11.98/5.58  #Define  : 0
% 11.98/5.58  #Split   : 4
% 11.98/5.58  #Chain   : 0
% 11.98/5.58  #Close   : 0
% 11.98/5.58  
% 11.98/5.58  Ordering : KBO
% 11.98/5.58  
% 11.98/5.58  Simplification rules
% 11.98/5.58  ----------------------
% 11.98/5.58  #Subsume      : 229
% 11.98/5.58  #Demod        : 7924
% 11.98/5.58  #Tautology    : 5294
% 11.98/5.58  #SimpNegUnit  : 3
% 11.98/5.58  #BackRed      : 1
% 11.98/5.58  
% 11.98/5.58  #Partial instantiations: 0
% 11.98/5.58  #Strategies tried      : 1
% 11.98/5.59  
% 11.98/5.59  Timing (in seconds)
% 11.98/5.59  ----------------------
% 11.98/5.59  Preprocessing        : 0.30
% 11.98/5.59  Parsing              : 0.16
% 11.98/5.59  CNF conversion       : 0.02
% 11.98/5.59  Main loop            : 4.51
% 11.98/5.59  Inferencing          : 0.73
% 11.98/5.59  Reduction            : 2.67
% 11.98/5.59  Demodulation         : 2.37
% 11.98/5.59  BG Simplification    : 0.09
% 11.98/5.59  Subsumption          : 0.82
% 11.98/5.59  Abstraction          : 0.12
% 11.98/5.59  MUC search           : 0.00
% 11.98/5.59  Cooper               : 0.00
% 11.98/5.59  Total                : 4.84
% 11.98/5.59  Index Insertion      : 0.00
% 11.98/5.59  Index Deletion       : 0.00
% 11.98/5.59  Index Matching       : 0.00
% 11.98/5.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
