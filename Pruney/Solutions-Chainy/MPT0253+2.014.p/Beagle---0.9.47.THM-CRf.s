%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 3.36s
% Output     : CNFRefutation 3.71s
% Verified   : 
% Statistics : Number of formulae       :   70 (  79 expanded)
%              Number of leaves         :   33 (  41 expanded)
%              Depth                    :   10
%              Number of atoms          :   84 ( 106 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_58,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_60,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_62,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_60,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_34,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_304,plain,(
    ! [A_65,B_66] :
      ( r2_hidden('#skF_1'(A_65,B_66),A_65)
      | r1_tarski(A_65,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( r2_hidden(D_11,A_6)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_313,plain,(
    ! [A_6,B_7,B_66] :
      ( r2_hidden('#skF_1'(k4_xboole_0(A_6,B_7),B_66),A_6)
      | r1_tarski(k4_xboole_0(A_6,B_7),B_66) ) ),
    inference(resolution,[status(thm)],[c_304,c_12])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( ~ r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k4_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1022,plain,(
    ! [A_156,B_157,B_158] :
      ( ~ r2_hidden('#skF_1'(k4_xboole_0(A_156,B_157),B_158),B_157)
      | r1_tarski(k4_xboole_0(A_156,B_157),B_158) ) ),
    inference(resolution,[status(thm)],[c_304,c_10])).

tff(c_1046,plain,(
    ! [A_159,B_160] : r1_tarski(k4_xboole_0(A_159,A_159),B_160) ),
    inference(resolution,[status(thm)],[c_313,c_1022])).

tff(c_38,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,A_19) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_280,plain,(
    ! [A_19] :
      ( k1_xboole_0 = A_19
      | ~ r1_tarski(A_19,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_38,c_275])).

tff(c_1079,plain,(
    ! [A_159] : k4_xboole_0(A_159,A_159) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1046,c_280])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_108,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(A_43,B_44) = A_43
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [B_13] : k3_xboole_0(B_13,B_13) = B_13 ),
    inference(resolution,[status(thm)],[c_30,c_108])).

tff(c_343,plain,(
    ! [A_74,B_75] : k5_xboole_0(A_74,k3_xboole_0(A_74,B_75)) = k4_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_352,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k4_xboole_0(B_13,B_13) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_343])).

tff(c_1086,plain,(
    ! [B_13] : k5_xboole_0(B_13,B_13) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1079,c_352])).

tff(c_721,plain,(
    ! [A_118,B_119,C_120] :
      ( r1_tarski(k2_tarski(A_118,B_119),C_120)
      | ~ r2_hidden(B_119,C_120)
      | ~ r2_hidden(A_118,C_120) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_36,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1949,plain,(
    ! [A_236,B_237,C_238] :
      ( k3_xboole_0(k2_tarski(A_236,B_237),C_238) = k2_tarski(A_236,B_237)
      | ~ r2_hidden(B_237,C_238)
      | ~ r2_hidden(A_236,C_238) ) ),
    inference(resolution,[status(thm)],[c_721,c_36])).

tff(c_32,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1955,plain,(
    ! [A_236,B_237,C_238] :
      ( k5_xboole_0(k2_tarski(A_236,B_237),k2_tarski(A_236,B_237)) = k4_xboole_0(k2_tarski(A_236,B_237),C_238)
      | ~ r2_hidden(B_237,C_238)
      | ~ r2_hidden(A_236,C_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1949,c_32])).

tff(c_1982,plain,(
    ! [A_239,B_240,C_241] :
      ( k4_xboole_0(k2_tarski(A_239,B_240),C_241) = k1_xboole_0
      | ~ r2_hidden(B_240,C_241)
      | ~ r2_hidden(A_239,C_241) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1086,c_1955])).

tff(c_40,plain,(
    ! [A_20,B_21] : k2_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2067,plain,(
    ! [C_241,A_239,B_240] :
      ( k2_xboole_0(C_241,k2_tarski(A_239,B_240)) = k2_xboole_0(C_241,k1_xboole_0)
      | ~ r2_hidden(B_240,C_241)
      | ~ r2_hidden(A_239,C_241) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1982,c_40])).

tff(c_2111,plain,(
    ! [C_242,A_243,B_244] :
      ( k2_xboole_0(C_242,k2_tarski(A_243,B_244)) = C_242
      | ~ r2_hidden(B_244,C_242)
      | ~ r2_hidden(A_243,C_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2067])).

tff(c_42,plain,(
    ! [B_23,A_22] : k2_tarski(B_23,A_22) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_152,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_167,plain,(
    ! [B_51,A_52] : k3_tarski(k2_tarski(B_51,A_52)) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_152])).

tff(c_50,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_173,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_50])).

tff(c_58,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_6'),'#skF_5') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_190,plain,(
    k2_xboole_0('#skF_5',k2_tarski('#skF_4','#skF_6')) != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_58])).

tff(c_2121,plain,
    ( ~ r2_hidden('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2111,c_190])).

tff(c_2164,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_2121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:27:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.36/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.60  
% 3.36/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.36/1.60  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.36/1.60  
% 3.36/1.60  %Foreground sorts:
% 3.36/1.60  
% 3.36/1.60  
% 3.36/1.60  %Background operators:
% 3.36/1.60  
% 3.36/1.60  
% 3.36/1.60  %Foreground operators:
% 3.36/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.36/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.36/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.36/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.36/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.36/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.36/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.36/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.36/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.36/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.36/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.36/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.36/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.36/1.60  
% 3.71/1.62  tff(f_83, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 3.71/1.62  tff(f_52, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 3.71/1.62  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.71/1.62  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.71/1.62  tff(f_58, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.71/1.62  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.71/1.62  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.71/1.62  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.71/1.62  tff(f_76, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.71/1.62  tff(f_60, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.71/1.62  tff(f_62, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.71/1.62  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.71/1.62  tff(c_62, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.71/1.62  tff(c_60, plain, (r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.71/1.62  tff(c_34, plain, (![A_16]: (k2_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.71/1.62  tff(c_304, plain, (![A_65, B_66]: (r2_hidden('#skF_1'(A_65, B_66), A_65) | r1_tarski(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.71/1.62  tff(c_12, plain, (![D_11, A_6, B_7]: (r2_hidden(D_11, A_6) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.71/1.62  tff(c_313, plain, (![A_6, B_7, B_66]: (r2_hidden('#skF_1'(k4_xboole_0(A_6, B_7), B_66), A_6) | r1_tarski(k4_xboole_0(A_6, B_7), B_66))), inference(resolution, [status(thm)], [c_304, c_12])).
% 3.71/1.62  tff(c_10, plain, (![D_11, B_7, A_6]: (~r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k4_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.71/1.62  tff(c_1022, plain, (![A_156, B_157, B_158]: (~r2_hidden('#skF_1'(k4_xboole_0(A_156, B_157), B_158), B_157) | r1_tarski(k4_xboole_0(A_156, B_157), B_158))), inference(resolution, [status(thm)], [c_304, c_10])).
% 3.71/1.62  tff(c_1046, plain, (![A_159, B_160]: (r1_tarski(k4_xboole_0(A_159, A_159), B_160))), inference(resolution, [status(thm)], [c_313, c_1022])).
% 3.71/1.62  tff(c_38, plain, (![A_19]: (r1_tarski(k1_xboole_0, A_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.71/1.62  tff(c_275, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.71/1.62  tff(c_280, plain, (![A_19]: (k1_xboole_0=A_19 | ~r1_tarski(A_19, k1_xboole_0))), inference(resolution, [status(thm)], [c_38, c_275])).
% 3.71/1.62  tff(c_1079, plain, (![A_159]: (k4_xboole_0(A_159, A_159)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1046, c_280])).
% 3.71/1.62  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.71/1.62  tff(c_108, plain, (![A_43, B_44]: (k3_xboole_0(A_43, B_44)=A_43 | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.71/1.62  tff(c_116, plain, (![B_13]: (k3_xboole_0(B_13, B_13)=B_13)), inference(resolution, [status(thm)], [c_30, c_108])).
% 3.71/1.62  tff(c_343, plain, (![A_74, B_75]: (k5_xboole_0(A_74, k3_xboole_0(A_74, B_75))=k4_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.71/1.62  tff(c_352, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k4_xboole_0(B_13, B_13))), inference(superposition, [status(thm), theory('equality')], [c_116, c_343])).
% 3.71/1.62  tff(c_1086, plain, (![B_13]: (k5_xboole_0(B_13, B_13)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1079, c_352])).
% 3.71/1.62  tff(c_721, plain, (![A_118, B_119, C_120]: (r1_tarski(k2_tarski(A_118, B_119), C_120) | ~r2_hidden(B_119, C_120) | ~r2_hidden(A_118, C_120))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.71/1.62  tff(c_36, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.71/1.62  tff(c_1949, plain, (![A_236, B_237, C_238]: (k3_xboole_0(k2_tarski(A_236, B_237), C_238)=k2_tarski(A_236, B_237) | ~r2_hidden(B_237, C_238) | ~r2_hidden(A_236, C_238))), inference(resolution, [status(thm)], [c_721, c_36])).
% 3.71/1.62  tff(c_32, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.71/1.62  tff(c_1955, plain, (![A_236, B_237, C_238]: (k5_xboole_0(k2_tarski(A_236, B_237), k2_tarski(A_236, B_237))=k4_xboole_0(k2_tarski(A_236, B_237), C_238) | ~r2_hidden(B_237, C_238) | ~r2_hidden(A_236, C_238))), inference(superposition, [status(thm), theory('equality')], [c_1949, c_32])).
% 3.71/1.62  tff(c_1982, plain, (![A_239, B_240, C_241]: (k4_xboole_0(k2_tarski(A_239, B_240), C_241)=k1_xboole_0 | ~r2_hidden(B_240, C_241) | ~r2_hidden(A_239, C_241))), inference(demodulation, [status(thm), theory('equality')], [c_1086, c_1955])).
% 3.71/1.62  tff(c_40, plain, (![A_20, B_21]: (k2_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.71/1.62  tff(c_2067, plain, (![C_241, A_239, B_240]: (k2_xboole_0(C_241, k2_tarski(A_239, B_240))=k2_xboole_0(C_241, k1_xboole_0) | ~r2_hidden(B_240, C_241) | ~r2_hidden(A_239, C_241))), inference(superposition, [status(thm), theory('equality')], [c_1982, c_40])).
% 3.71/1.62  tff(c_2111, plain, (![C_242, A_243, B_244]: (k2_xboole_0(C_242, k2_tarski(A_243, B_244))=C_242 | ~r2_hidden(B_244, C_242) | ~r2_hidden(A_243, C_242))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2067])).
% 3.71/1.62  tff(c_42, plain, (![B_23, A_22]: (k2_tarski(B_23, A_22)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.71/1.62  tff(c_152, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.62  tff(c_167, plain, (![B_51, A_52]: (k3_tarski(k2_tarski(B_51, A_52))=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_42, c_152])).
% 3.71/1.62  tff(c_50, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.71/1.62  tff(c_173, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_167, c_50])).
% 3.71/1.62  tff(c_58, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_6'), '#skF_5')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.71/1.62  tff(c_190, plain, (k2_xboole_0('#skF_5', k2_tarski('#skF_4', '#skF_6'))!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_173, c_58])).
% 3.71/1.62  tff(c_2121, plain, (~r2_hidden('#skF_6', '#skF_5') | ~r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2111, c_190])).
% 3.71/1.62  tff(c_2164, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_2121])).
% 3.71/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.71/1.62  
% 3.71/1.62  Inference rules
% 3.71/1.62  ----------------------
% 3.71/1.62  #Ref     : 0
% 3.71/1.62  #Sup     : 501
% 3.71/1.62  #Fact    : 0
% 3.71/1.62  #Define  : 0
% 3.71/1.62  #Split   : 6
% 3.71/1.62  #Chain   : 0
% 3.71/1.62  #Close   : 0
% 3.71/1.62  
% 3.71/1.62  Ordering : KBO
% 3.71/1.62  
% 3.71/1.62  Simplification rules
% 3.71/1.62  ----------------------
% 3.71/1.62  #Subsume      : 155
% 3.71/1.62  #Demod        : 229
% 3.71/1.62  #Tautology    : 218
% 3.71/1.62  #SimpNegUnit  : 9
% 3.71/1.62  #BackRed      : 4
% 3.71/1.62  
% 3.71/1.62  #Partial instantiations: 0
% 3.71/1.62  #Strategies tried      : 1
% 3.71/1.62  
% 3.71/1.62  Timing (in seconds)
% 3.71/1.62  ----------------------
% 3.71/1.62  Preprocessing        : 0.32
% 3.71/1.62  Parsing              : 0.16
% 3.71/1.62  CNF conversion       : 0.02
% 3.71/1.62  Main loop            : 0.55
% 3.71/1.62  Inferencing          : 0.19
% 3.71/1.62  Reduction            : 0.19
% 3.71/1.62  Demodulation         : 0.14
% 3.71/1.62  BG Simplification    : 0.02
% 3.71/1.62  Subsumption          : 0.11
% 3.71/1.62  Abstraction          : 0.03
% 3.71/1.62  MUC search           : 0.00
% 3.71/1.62  Cooper               : 0.00
% 3.71/1.62  Total                : 0.89
% 3.71/1.62  Index Insertion      : 0.00
% 3.71/1.62  Index Deletion       : 0.00
% 3.71/1.62  Index Matching       : 0.00
% 3.71/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
