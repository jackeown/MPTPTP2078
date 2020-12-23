%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:00 EST 2020

% Result     : Theorem 5.92s
% Output     : CNFRefutation 6.10s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 158 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :   18
%              Number of atoms          :   77 ( 188 expanded)
%              Number of equality atoms :   41 ( 120 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_75,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_81,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_38,plain,(
    ! [A_23,B_24] : k2_xboole_0(A_23,k3_xboole_0(A_23,B_24)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_44,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = k4_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_36,plain,(
    ! [A_21,B_22] : r1_tarski(k3_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_99,plain,(
    ! [A_21,B_22] : k4_xboole_0(k3_xboole_0(A_21,B_22),A_21) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_91])).

tff(c_133,plain,(
    ! [A_50,B_51] : k2_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_148,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_133])).

tff(c_153,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_148])).

tff(c_162,plain,(
    ! [A_52] : k2_xboole_0(k1_xboole_0,A_52) = A_52 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_40,plain,(
    ! [A_25,B_26] : k2_xboole_0(A_25,k4_xboole_0(B_26,A_25)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_180,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_215,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_180])).

tff(c_235,plain,(
    ! [B_26] : k4_xboole_0(B_26,k1_xboole_0) = B_26 ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_215])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_240,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4285,plain,(
    ! [A_198,A_199,B_200] :
      ( ~ r2_hidden('#skF_3'(A_198,k4_xboole_0(A_199,B_200)),B_200)
      | r1_xboole_0(A_198,k4_xboole_0(A_199,B_200)) ) ),
    inference(resolution,[status(thm)],[c_24,c_240])).

tff(c_4364,plain,(
    ! [A_201,A_202] : r1_xboole_0(A_201,k4_xboole_0(A_202,A_201)) ),
    inference(resolution,[status(thm)],[c_26,c_4285])).

tff(c_219,plain,(
    ! [B_24] : k3_xboole_0(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_180])).

tff(c_332,plain,(
    ! [A_62,B_63] : k4_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_350,plain,(
    ! [B_24] : k4_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_332])).

tff(c_354,plain,(
    ! [B_24] : k4_xboole_0(k1_xboole_0,B_24) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_350])).

tff(c_42,plain,(
    ! [A_27,B_28] : k4_xboole_0(k2_xboole_0(A_27,B_28),B_28) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_194,plain,(
    ! [A_53] : k4_xboole_0(k1_xboole_0,A_53) = k4_xboole_0(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_42])).

tff(c_396,plain,(
    ! [A_53] : k4_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_194])).

tff(c_20,plain,(
    ! [A_3,B_4,C_5] :
      ( r2_hidden('#skF_1'(A_3,B_4,C_5),A_3)
      | r2_hidden('#skF_2'(A_3,B_4,C_5),C_5)
      | k4_xboole_0(A_3,B_4) = C_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_969,plain,(
    ! [A_104,B_105,C_106] :
      ( ~ r2_hidden('#skF_1'(A_104,B_105,C_106),B_105)
      | r2_hidden('#skF_2'(A_104,B_105,C_106),C_106)
      | k4_xboole_0(A_104,B_105) = C_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_972,plain,(
    ! [A_3,C_5] :
      ( r2_hidden('#skF_2'(A_3,A_3,C_5),C_5)
      | k4_xboole_0(A_3,A_3) = C_5 ) ),
    inference(resolution,[status(thm)],[c_20,c_969])).

tff(c_1696,plain,(
    ! [A_139,C_140] :
      ( r2_hidden('#skF_2'(A_139,A_139,C_140),C_140)
      | k1_xboole_0 = C_140 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_972])).

tff(c_30,plain,(
    ! [A_14,B_15,C_18] :
      ( ~ r1_xboole_0(A_14,B_15)
      | ~ r2_hidden(C_18,k3_xboole_0(A_14,B_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1722,plain,(
    ! [A_14,B_15] :
      ( ~ r1_xboole_0(A_14,B_15)
      | k3_xboole_0(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1696,c_30])).

tff(c_4423,plain,(
    ! [A_203,A_204] : k3_xboole_0(A_203,k4_xboole_0(A_204,A_203)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_4364,c_1722])).

tff(c_4452,plain,(
    ! [A_203,A_204] : k4_xboole_0(A_203,k4_xboole_0(A_204,A_203)) = k4_xboole_0(A_203,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4423,c_44])).

tff(c_4521,plain,(
    ! [A_203,A_204] : k4_xboole_0(A_203,k4_xboole_0(A_204,A_203)) = A_203 ),
    inference(demodulation,[status(thm),theory(equality)],[c_235,c_4452])).

tff(c_139,plain,(
    ! [A_50,B_51] : k4_xboole_0(k2_xboole_0(A_50,B_51),k4_xboole_0(B_51,A_50)) = k4_xboole_0(A_50,k4_xboole_0(B_51,A_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_42])).

tff(c_5160,plain,(
    ! [A_218,B_219] : k4_xboole_0(k2_xboole_0(A_218,B_219),k4_xboole_0(B_219,A_218)) = A_218 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4521,c_139])).

tff(c_5310,plain,(
    ! [A_29,B_30] : k4_xboole_0(k2_xboole_0(k3_xboole_0(A_29,B_30),A_29),k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_5160])).

tff(c_5373,plain,(
    ! [A_29,B_30] : k4_xboole_0(A_29,k4_xboole_0(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_2,c_5310])).

tff(c_46,plain,(
    k4_xboole_0('#skF_5',k4_xboole_0('#skF_5','#skF_6')) != k3_xboole_0('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:06:53 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.92/2.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.31  
% 6.10/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.31  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 6.10/2.31  
% 6.10/2.31  %Foreground sorts:
% 6.10/2.31  
% 6.10/2.31  
% 6.10/2.31  %Background operators:
% 6.10/2.31  
% 6.10/2.31  
% 6.10/2.31  %Foreground operators:
% 6.10/2.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.10/2.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.10/2.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.10/2.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.10/2.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.10/2.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 6.10/2.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.10/2.31  tff('#skF_5', type, '#skF_5': $i).
% 6.10/2.31  tff('#skF_6', type, '#skF_6': $i).
% 6.10/2.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.10/2.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.10/2.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.10/2.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.10/2.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.10/2.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.10/2.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 6.10/2.31  
% 6.10/2.33  tff(f_77, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 6.10/2.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.10/2.33  tff(f_83, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 6.10/2.33  tff(f_75, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.10/2.33  tff(f_73, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.10/2.33  tff(f_79, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.10/2.33  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 6.10/2.33  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.10/2.33  tff(f_81, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.10/2.33  tff(f_69, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.10/2.33  tff(f_86, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.10/2.33  tff(c_38, plain, (![A_23, B_24]: (k2_xboole_0(A_23, k3_xboole_0(A_23, B_24))=A_23)), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.10/2.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.10/2.33  tff(c_44, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k3_xboole_0(A_29, B_30))=k4_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.10/2.33  tff(c_36, plain, (![A_21, B_22]: (r1_tarski(k3_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.10/2.33  tff(c_91, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.10/2.33  tff(c_99, plain, (![A_21, B_22]: (k4_xboole_0(k3_xboole_0(A_21, B_22), A_21)=k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_91])).
% 6.10/2.33  tff(c_133, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k4_xboole_0(B_51, A_50))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.10/2.33  tff(c_148, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_99, c_133])).
% 6.10/2.33  tff(c_153, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_148])).
% 6.10/2.33  tff(c_162, plain, (![A_52]: (k2_xboole_0(k1_xboole_0, A_52)=A_52)), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 6.10/2.33  tff(c_40, plain, (![A_25, B_26]: (k2_xboole_0(A_25, k4_xboole_0(B_26, A_25))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.10/2.33  tff(c_180, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_153, c_2])).
% 6.10/2.33  tff(c_215, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_26))), inference(superposition, [status(thm), theory('equality')], [c_40, c_180])).
% 6.10/2.33  tff(c_235, plain, (![B_26]: (k4_xboole_0(B_26, k1_xboole_0)=B_26)), inference(demodulation, [status(thm), theory('equality')], [c_162, c_215])).
% 6.10/2.33  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.10/2.33  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.10/2.33  tff(c_240, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k4_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.10/2.33  tff(c_4285, plain, (![A_198, A_199, B_200]: (~r2_hidden('#skF_3'(A_198, k4_xboole_0(A_199, B_200)), B_200) | r1_xboole_0(A_198, k4_xboole_0(A_199, B_200)))), inference(resolution, [status(thm)], [c_24, c_240])).
% 6.10/2.33  tff(c_4364, plain, (![A_201, A_202]: (r1_xboole_0(A_201, k4_xboole_0(A_202, A_201)))), inference(resolution, [status(thm)], [c_26, c_4285])).
% 6.10/2.33  tff(c_219, plain, (![B_24]: (k3_xboole_0(k1_xboole_0, B_24)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_38, c_180])).
% 6.10/2.33  tff(c_332, plain, (![A_62, B_63]: (k4_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.10/2.33  tff(c_350, plain, (![B_24]: (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_24))), inference(superposition, [status(thm), theory('equality')], [c_219, c_332])).
% 6.10/2.33  tff(c_354, plain, (![B_24]: (k4_xboole_0(k1_xboole_0, B_24)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_235, c_350])).
% 6.10/2.33  tff(c_42, plain, (![A_27, B_28]: (k4_xboole_0(k2_xboole_0(A_27, B_28), B_28)=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.10/2.33  tff(c_194, plain, (![A_53]: (k4_xboole_0(k1_xboole_0, A_53)=k4_xboole_0(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_180, c_42])).
% 6.10/2.33  tff(c_396, plain, (![A_53]: (k4_xboole_0(A_53, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_354, c_194])).
% 6.10/2.33  tff(c_20, plain, (![A_3, B_4, C_5]: (r2_hidden('#skF_1'(A_3, B_4, C_5), A_3) | r2_hidden('#skF_2'(A_3, B_4, C_5), C_5) | k4_xboole_0(A_3, B_4)=C_5)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.10/2.33  tff(c_969, plain, (![A_104, B_105, C_106]: (~r2_hidden('#skF_1'(A_104, B_105, C_106), B_105) | r2_hidden('#skF_2'(A_104, B_105, C_106), C_106) | k4_xboole_0(A_104, B_105)=C_106)), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.10/2.33  tff(c_972, plain, (![A_3, C_5]: (r2_hidden('#skF_2'(A_3, A_3, C_5), C_5) | k4_xboole_0(A_3, A_3)=C_5)), inference(resolution, [status(thm)], [c_20, c_969])).
% 6.10/2.33  tff(c_1696, plain, (![A_139, C_140]: (r2_hidden('#skF_2'(A_139, A_139, C_140), C_140) | k1_xboole_0=C_140)), inference(demodulation, [status(thm), theory('equality')], [c_396, c_972])).
% 6.10/2.33  tff(c_30, plain, (![A_14, B_15, C_18]: (~r1_xboole_0(A_14, B_15) | ~r2_hidden(C_18, k3_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.10/2.33  tff(c_1722, plain, (![A_14, B_15]: (~r1_xboole_0(A_14, B_15) | k3_xboole_0(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1696, c_30])).
% 6.10/2.33  tff(c_4423, plain, (![A_203, A_204]: (k3_xboole_0(A_203, k4_xboole_0(A_204, A_203))=k1_xboole_0)), inference(resolution, [status(thm)], [c_4364, c_1722])).
% 6.10/2.33  tff(c_4452, plain, (![A_203, A_204]: (k4_xboole_0(A_203, k4_xboole_0(A_204, A_203))=k4_xboole_0(A_203, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4423, c_44])).
% 6.10/2.33  tff(c_4521, plain, (![A_203, A_204]: (k4_xboole_0(A_203, k4_xboole_0(A_204, A_203))=A_203)), inference(demodulation, [status(thm), theory('equality')], [c_235, c_4452])).
% 6.10/2.33  tff(c_139, plain, (![A_50, B_51]: (k4_xboole_0(k2_xboole_0(A_50, B_51), k4_xboole_0(B_51, A_50))=k4_xboole_0(A_50, k4_xboole_0(B_51, A_50)))), inference(superposition, [status(thm), theory('equality')], [c_133, c_42])).
% 6.10/2.33  tff(c_5160, plain, (![A_218, B_219]: (k4_xboole_0(k2_xboole_0(A_218, B_219), k4_xboole_0(B_219, A_218))=A_218)), inference(demodulation, [status(thm), theory('equality')], [c_4521, c_139])).
% 6.10/2.33  tff(c_5310, plain, (![A_29, B_30]: (k4_xboole_0(k2_xboole_0(k3_xboole_0(A_29, B_30), A_29), k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(superposition, [status(thm), theory('equality')], [c_44, c_5160])).
% 6.10/2.33  tff(c_5373, plain, (![A_29, B_30]: (k4_xboole_0(A_29, k4_xboole_0(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_2, c_5310])).
% 6.10/2.33  tff(c_46, plain, (k4_xboole_0('#skF_5', k4_xboole_0('#skF_5', '#skF_6'))!=k3_xboole_0('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_86])).
% 6.10/2.33  tff(c_9645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5373, c_46])).
% 6.10/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.10/2.33  
% 6.10/2.33  Inference rules
% 6.10/2.33  ----------------------
% 6.10/2.33  #Ref     : 0
% 6.10/2.33  #Sup     : 2420
% 6.10/2.33  #Fact    : 0
% 6.10/2.33  #Define  : 0
% 6.10/2.33  #Split   : 1
% 6.10/2.33  #Chain   : 0
% 6.10/2.33  #Close   : 0
% 6.10/2.33  
% 6.10/2.33  Ordering : KBO
% 6.10/2.33  
% 6.10/2.33  Simplification rules
% 6.10/2.33  ----------------------
% 6.10/2.33  #Subsume      : 268
% 6.10/2.33  #Demod        : 2227
% 6.10/2.33  #Tautology    : 1633
% 6.10/2.33  #SimpNegUnit  : 46
% 6.10/2.33  #BackRed      : 4
% 6.10/2.33  
% 6.10/2.33  #Partial instantiations: 0
% 6.10/2.33  #Strategies tried      : 1
% 6.10/2.33  
% 6.10/2.33  Timing (in seconds)
% 6.10/2.33  ----------------------
% 6.10/2.33  Preprocessing        : 0.30
% 6.10/2.33  Parsing              : 0.17
% 6.10/2.33  CNF conversion       : 0.02
% 6.10/2.33  Main loop            : 1.21
% 6.10/2.33  Inferencing          : 0.36
% 6.10/2.33  Reduction            : 0.53
% 6.10/2.33  Demodulation         : 0.44
% 6.10/2.33  BG Simplification    : 0.04
% 6.10/2.33  Subsumption          : 0.21
% 6.10/2.33  Abstraction          : 0.05
% 6.10/2.33  MUC search           : 0.00
% 6.10/2.33  Cooper               : 0.00
% 6.10/2.33  Total                : 1.54
% 6.10/2.33  Index Insertion      : 0.00
% 6.10/2.33  Index Deletion       : 0.00
% 6.10/2.33  Index Matching       : 0.00
% 6.10/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
