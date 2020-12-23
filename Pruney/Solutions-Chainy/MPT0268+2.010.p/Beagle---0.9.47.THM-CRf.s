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
% DateTime   : Thu Dec  3 09:52:35 EST 2020

% Result     : Theorem 4.93s
% Output     : CNFRefutation 5.16s
% Verified   : 
% Statistics : Number of formulae       :   79 (  99 expanded)
%              Number of leaves         :   32 (  46 expanded)
%              Depth                    :    7
%              Number of atoms          :   90 ( 131 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3

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

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_70,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_68,axiom,(
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

tff(c_74,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_127,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_26,plain,(
    ! [B_10] : r1_tarski(B_10,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_157,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k1_xboole_0
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_169,plain,(
    ! [B_10] : k4_xboole_0(B_10,B_10) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_620,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),B_96) = k1_tarski(A_95)
      | r2_hidden(A_95,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_36,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_632,plain,(
    ! [A_95,B_96] :
      ( k4_xboole_0(k1_tarski(A_95),k1_tarski(A_95)) = k3_xboole_0(k1_tarski(A_95),B_96)
      | r2_hidden(A_95,B_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_620,c_36])).

tff(c_1248,plain,(
    ! [A_129,B_130] :
      ( k3_xboole_0(k1_tarski(A_129),B_130) = k1_xboole_0
      | r2_hidden(A_129,B_130) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_632])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1295,plain,(
    ! [B_130,A_129] :
      ( k3_xboole_0(B_130,k1_tarski(A_129)) = k1_xboole_0
      | r2_hidden(A_129,B_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1248,c_2])).

tff(c_34,plain,(
    ! [A_15,B_16] : r1_tarski(k4_xboole_0(A_15,B_16),A_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | k4_xboole_0(A_11,B_12) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_472,plain,(
    ! [B_79,A_80] :
      ( B_79 = A_80
      | ~ r1_tarski(B_79,A_80)
      | ~ r1_tarski(A_80,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2543,plain,(
    ! [B_182,A_183] :
      ( B_182 = A_183
      | ~ r1_tarski(B_182,A_183)
      | k4_xboole_0(A_183,B_182) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_28,c_472])).

tff(c_2561,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_34,c_2543])).

tff(c_2576,plain,(
    ! [A_184,B_185] :
      ( k4_xboole_0(A_184,B_185) = A_184
      | k3_xboole_0(A_184,B_185) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2561])).

tff(c_72,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | r2_hidden('#skF_8','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_204,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2771,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2576,c_204])).

tff(c_3036,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1295,c_2771])).

tff(c_3040,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_3036])).

tff(c_3041,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_62,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_129,plain,(
    ! [A_51,B_52] : k1_enumset1(A_51,A_51,B_52) = k2_tarski(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [E_25,A_19,B_20] : r2_hidden(E_25,k1_enumset1(A_19,B_20,E_25)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_147,plain,(
    ! [B_53,A_54] : r2_hidden(B_53,k2_tarski(A_54,B_53)) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_40])).

tff(c_150,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_147])).

tff(c_3042,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_6')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_76,plain,
    ( k4_xboole_0('#skF_5',k1_tarski('#skF_6')) != '#skF_5'
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3166,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3042,c_76])).

tff(c_3498,plain,(
    ! [D_216,B_217,A_218] :
      ( ~ r2_hidden(D_216,B_217)
      | ~ r2_hidden(D_216,k4_xboole_0(A_218,B_217)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3745,plain,(
    ! [D_232] :
      ( ~ r2_hidden(D_232,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_232,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3166,c_3498])).

tff(c_3749,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_150,c_3745])).

tff(c_3753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3041,c_3749])).

tff(c_3754,plain,(
    r2_hidden('#skF_8','#skF_7') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_3780,plain,(
    ! [A_238,B_239] : k1_enumset1(A_238,A_238,B_239) = k2_tarski(A_238,B_239) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_44,plain,(
    ! [E_25,B_20,C_21] : r2_hidden(E_25,k1_enumset1(E_25,B_20,C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_3822,plain,(
    ! [A_242,B_243] : r2_hidden(A_242,k2_tarski(A_242,B_243)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3780,c_44])).

tff(c_3825,plain,(
    ! [A_26] : r2_hidden(A_26,k1_tarski(A_26)) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3822])).

tff(c_3755,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_78,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_3909,plain,(
    k4_xboole_0('#skF_7',k1_tarski('#skF_8')) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3755,c_78])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3988,plain,(
    ! [D_264] :
      ( ~ r2_hidden(D_264,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_264,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3909,c_6])).

tff(c_3992,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_3825,c_3988])).

tff(c_3996,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3754,c_3992])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:17:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.93/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.99  
% 5.16/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/1.99  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_8 > #skF_3
% 5.16/1.99  
% 5.16/1.99  %Foreground sorts:
% 5.16/1.99  
% 5.16/1.99  
% 5.16/1.99  %Background operators:
% 5.16/1.99  
% 5.16/1.99  
% 5.16/1.99  %Foreground operators:
% 5.16/1.99  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.16/1.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.16/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.16/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.16/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.16/1.99  tff('#skF_7', type, '#skF_7': $i).
% 5.16/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.16/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.16/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.16/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.16/1.99  tff('#skF_5', type, '#skF_5': $i).
% 5.16/1.99  tff('#skF_6', type, '#skF_6': $i).
% 5.16/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.16/1.99  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.16/1.99  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 5.16/1.99  tff('#skF_8', type, '#skF_8': $i).
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.16/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.16/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.16/1.99  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.16/1.99  
% 5.16/2.01  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 5.16/2.01  tff(f_43, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.16/2.01  tff(f_47, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 5.16/2.01  tff(f_79, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 5.16/2.01  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.16/2.01  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.16/2.01  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.16/2.01  tff(f_70, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.16/2.01  tff(f_72, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.16/2.01  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.16/2.01  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 5.16/2.01  tff(c_74, plain, (~r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.16/2.01  tff(c_127, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_74])).
% 5.16/2.01  tff(c_26, plain, (![B_10]: (r1_tarski(B_10, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.16/2.01  tff(c_157, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k1_xboole_0 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.16/2.01  tff(c_169, plain, (![B_10]: (k4_xboole_0(B_10, B_10)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_157])).
% 5.16/2.01  tff(c_620, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), B_96)=k1_tarski(A_95) | r2_hidden(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.16/2.01  tff(c_36, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.16/2.01  tff(c_632, plain, (![A_95, B_96]: (k4_xboole_0(k1_tarski(A_95), k1_tarski(A_95))=k3_xboole_0(k1_tarski(A_95), B_96) | r2_hidden(A_95, B_96))), inference(superposition, [status(thm), theory('equality')], [c_620, c_36])).
% 5.16/2.01  tff(c_1248, plain, (![A_129, B_130]: (k3_xboole_0(k1_tarski(A_129), B_130)=k1_xboole_0 | r2_hidden(A_129, B_130))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_632])).
% 5.16/2.01  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.16/2.01  tff(c_1295, plain, (![B_130, A_129]: (k3_xboole_0(B_130, k1_tarski(A_129))=k1_xboole_0 | r2_hidden(A_129, B_130))), inference(superposition, [status(thm), theory('equality')], [c_1248, c_2])).
% 5.16/2.01  tff(c_34, plain, (![A_15, B_16]: (r1_tarski(k4_xboole_0(A_15, B_16), A_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.16/2.01  tff(c_28, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | k4_xboole_0(A_11, B_12)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.16/2.01  tff(c_472, plain, (![B_79, A_80]: (B_79=A_80 | ~r1_tarski(B_79, A_80) | ~r1_tarski(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.16/2.01  tff(c_2543, plain, (![B_182, A_183]: (B_182=A_183 | ~r1_tarski(B_182, A_183) | k4_xboole_0(A_183, B_182)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_28, c_472])).
% 5.16/2.01  tff(c_2561, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_2543])).
% 5.16/2.01  tff(c_2576, plain, (![A_184, B_185]: (k4_xboole_0(A_184, B_185)=A_184 | k3_xboole_0(A_184, B_185)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2561])).
% 5.16/2.01  tff(c_72, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | r2_hidden('#skF_8', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.16/2.01  tff(c_204, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5'), inference(splitLeft, [status(thm)], [c_72])).
% 5.16/2.01  tff(c_2771, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2576, c_204])).
% 5.16/2.01  tff(c_3036, plain, (r2_hidden('#skF_6', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1295, c_2771])).
% 5.16/2.01  tff(c_3040, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_3036])).
% 5.16/2.01  tff(c_3041, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 5.16/2.01  tff(c_62, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.16/2.01  tff(c_129, plain, (![A_51, B_52]: (k1_enumset1(A_51, A_51, B_52)=k2_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.16/2.01  tff(c_40, plain, (![E_25, A_19, B_20]: (r2_hidden(E_25, k1_enumset1(A_19, B_20, E_25)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.16/2.01  tff(c_147, plain, (![B_53, A_54]: (r2_hidden(B_53, k2_tarski(A_54, B_53)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_40])).
% 5.16/2.01  tff(c_150, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_147])).
% 5.16/2.01  tff(c_3042, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))='#skF_5'), inference(splitRight, [status(thm)], [c_72])).
% 5.16/2.01  tff(c_76, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_6'))!='#skF_5' | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.16/2.01  tff(c_3166, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3042, c_76])).
% 5.16/2.01  tff(c_3498, plain, (![D_216, B_217, A_218]: (~r2_hidden(D_216, B_217) | ~r2_hidden(D_216, k4_xboole_0(A_218, B_217)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/2.01  tff(c_3745, plain, (![D_232]: (~r2_hidden(D_232, k1_tarski('#skF_8')) | ~r2_hidden(D_232, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3166, c_3498])).
% 5.16/2.01  tff(c_3749, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_150, c_3745])).
% 5.16/2.01  tff(c_3753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3041, c_3749])).
% 5.16/2.01  tff(c_3754, plain, (r2_hidden('#skF_8', '#skF_7')), inference(splitRight, [status(thm)], [c_74])).
% 5.16/2.01  tff(c_3780, plain, (![A_238, B_239]: (k1_enumset1(A_238, A_238, B_239)=k2_tarski(A_238, B_239))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.16/2.01  tff(c_44, plain, (![E_25, B_20, C_21]: (r2_hidden(E_25, k1_enumset1(E_25, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.16/2.01  tff(c_3822, plain, (![A_242, B_243]: (r2_hidden(A_242, k2_tarski(A_242, B_243)))), inference(superposition, [status(thm), theory('equality')], [c_3780, c_44])).
% 5.16/2.01  tff(c_3825, plain, (![A_26]: (r2_hidden(A_26, k1_tarski(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_62, c_3822])).
% 5.16/2.01  tff(c_3755, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_74])).
% 5.16/2.01  tff(c_78, plain, (~r2_hidden('#skF_6', '#skF_5') | k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(cnfTransformation, [status(thm)], [f_85])).
% 5.16/2.01  tff(c_3909, plain, (k4_xboole_0('#skF_7', k1_tarski('#skF_8'))='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_3755, c_78])).
% 5.16/2.01  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.16/2.01  tff(c_3988, plain, (![D_264]: (~r2_hidden(D_264, k1_tarski('#skF_8')) | ~r2_hidden(D_264, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_3909, c_6])).
% 5.16/2.01  tff(c_3992, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_3825, c_3988])).
% 5.16/2.01  tff(c_3996, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3754, c_3992])).
% 5.16/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.16/2.01  
% 5.16/2.01  Inference rules
% 5.16/2.01  ----------------------
% 5.16/2.01  #Ref     : 0
% 5.16/2.01  #Sup     : 894
% 5.16/2.01  #Fact    : 0
% 5.16/2.01  #Define  : 0
% 5.16/2.01  #Split   : 2
% 5.16/2.01  #Chain   : 0
% 5.16/2.01  #Close   : 0
% 5.16/2.01  
% 5.16/2.01  Ordering : KBO
% 5.16/2.01  
% 5.16/2.01  Simplification rules
% 5.16/2.01  ----------------------
% 5.16/2.01  #Subsume      : 113
% 5.16/2.01  #Demod        : 601
% 5.16/2.01  #Tautology    : 595
% 5.16/2.01  #SimpNegUnit  : 64
% 5.16/2.01  #BackRed      : 14
% 5.16/2.01  
% 5.16/2.01  #Partial instantiations: 0
% 5.16/2.01  #Strategies tried      : 1
% 5.16/2.01  
% 5.16/2.01  Timing (in seconds)
% 5.16/2.01  ----------------------
% 5.16/2.02  Preprocessing        : 0.35
% 5.16/2.02  Parsing              : 0.17
% 5.16/2.02  CNF conversion       : 0.03
% 5.16/2.02  Main loop            : 0.84
% 5.16/2.02  Inferencing          : 0.30
% 5.16/2.02  Reduction            : 0.31
% 5.16/2.02  Demodulation         : 0.23
% 5.16/2.02  BG Simplification    : 0.04
% 5.16/2.02  Subsumption          : 0.14
% 5.16/2.02  Abstraction          : 0.04
% 5.16/2.02  MUC search           : 0.00
% 5.16/2.02  Cooper               : 0.00
% 5.16/2.02  Total                : 1.23
% 5.16/2.02  Index Insertion      : 0.00
% 5.16/2.02  Index Deletion       : 0.00
% 5.16/2.02  Index Matching       : 0.00
% 5.16/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
