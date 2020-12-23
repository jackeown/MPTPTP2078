%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:29 EST 2020

% Result     : Theorem 3.99s
% Output     : CNFRefutation 3.99s
% Verified   : 
% Statistics : Number of formulae       :   44 (  50 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   58 (  84 expanded)
%              Number of equality atoms :   23 (  24 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k3_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] :
              ( r2_hidden(C,D)
              & r2_hidden(D,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tarski)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
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

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_73,negated_conjecture,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    ! [A_14,C_29] :
      ( r2_hidden('#skF_6'(A_14,k3_tarski(A_14),C_29),A_14)
      | ~ r2_hidden(C_29,k3_tarski(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_8] : k3_xboole_0(A_8,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_62,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k4_xboole_0(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_77,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k3_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_62])).

tff(c_80,plain,(
    ! [A_9] : k4_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_77])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12,B_13] :
      ( r1_xboole_0(A_12,B_13)
      | k4_xboole_0(A_12,B_13) != A_12 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,(
    ! [A_48,B_49,C_50] :
      ( ~ r1_xboole_0(A_48,B_49)
      | ~ r2_hidden(C_50,B_49)
      | ~ r2_hidden(C_50,A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_162,plain,(
    ! [C_58,B_59,A_60] :
      ( ~ r2_hidden(C_58,B_59)
      | ~ r2_hidden(C_58,A_60)
      | k4_xboole_0(A_60,B_59) != A_60 ) ),
    inference(resolution,[status(thm)],[c_18,c_123])).

tff(c_239,plain,(
    ! [A_73,B_74,A_75] :
      ( ~ r2_hidden('#skF_1'(A_73,B_74),A_75)
      | k4_xboole_0(A_75,B_74) != A_75
      | r1_xboole_0(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_4,c_162])).

tff(c_253,plain,(
    ! [B_2,A_1] :
      ( k4_xboole_0(B_2,B_2) != B_2
      | r1_xboole_0(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_239])).

tff(c_260,plain,(
    ! [B_76,A_77] :
      ( k1_xboole_0 != B_76
      | r1_xboole_0(A_77,B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_253])).

tff(c_2,plain,(
    ! [A_1,B_2,C_5] :
      ( ~ r1_xboole_0(A_1,B_2)
      | ~ r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_356,plain,(
    ! [C_84,B_85,A_86] :
      ( ~ r2_hidden(C_84,B_85)
      | ~ r2_hidden(C_84,A_86)
      | k1_xboole_0 != B_85 ) ),
    inference(resolution,[status(thm)],[c_260,c_2])).

tff(c_3780,plain,(
    ! [A_216,C_217,A_218] :
      ( ~ r2_hidden('#skF_6'(A_216,k3_tarski(A_216),C_217),A_218)
      | k1_xboole_0 != A_216
      | ~ r2_hidden(C_217,k3_tarski(A_216)) ) ),
    inference(resolution,[status(thm)],[c_22,c_356])).

tff(c_3806,plain,(
    ! [A_219,C_220] :
      ( k1_xboole_0 != A_219
      | ~ r2_hidden(C_220,k3_tarski(A_219)) ) ),
    inference(resolution,[status(thm)],[c_22,c_3780])).

tff(c_3859,plain,(
    k3_tarski(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_3806])).

tff(c_38,plain,(
    k3_tarski(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_3862,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3859,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n001.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:25:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.99/1.74  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.74  
% 3.99/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.75  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.99/1.75  
% 3.99/1.75  %Foreground sorts:
% 3.99/1.75  
% 3.99/1.75  
% 3.99/1.75  %Background operators:
% 3.99/1.75  
% 3.99/1.75  
% 3.99/1.75  %Foreground operators:
% 3.99/1.75  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.99/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.99/1.75  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.99/1.75  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.99/1.75  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.99/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.99/1.75  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.99/1.75  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.99/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.99/1.75  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.99/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.99/1.75  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.99/1.75  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.99/1.75  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.99/1.75  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.99/1.75  
% 3.99/1.76  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.99/1.76  tff(f_71, axiom, (![A, B]: ((B = k3_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: (r2_hidden(C, D) & r2_hidden(D, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tarski)).
% 3.99/1.76  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.99/1.76  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.99/1.76  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.99/1.76  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.99/1.76  tff(f_61, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.99/1.76  tff(f_73, negated_conjecture, ~(k3_tarski(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_zfmisc_1)).
% 3.99/1.76  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.99/1.76  tff(c_22, plain, (![A_14, C_29]: (r2_hidden('#skF_6'(A_14, k3_tarski(A_14), C_29), A_14) | ~r2_hidden(C_29, k3_tarski(A_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.99/1.76  tff(c_10, plain, (![A_8]: (k3_xboole_0(A_8, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.99/1.76  tff(c_12, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.99/1.76  tff(c_62, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k4_xboole_0(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.99/1.76  tff(c_77, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k3_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_62])).
% 3.99/1.76  tff(c_80, plain, (![A_9]: (k4_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_77])).
% 3.99/1.76  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.76  tff(c_18, plain, (![A_12, B_13]: (r1_xboole_0(A_12, B_13) | k4_xboole_0(A_12, B_13)!=A_12)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.99/1.76  tff(c_123, plain, (![A_48, B_49, C_50]: (~r1_xboole_0(A_48, B_49) | ~r2_hidden(C_50, B_49) | ~r2_hidden(C_50, A_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.76  tff(c_162, plain, (![C_58, B_59, A_60]: (~r2_hidden(C_58, B_59) | ~r2_hidden(C_58, A_60) | k4_xboole_0(A_60, B_59)!=A_60)), inference(resolution, [status(thm)], [c_18, c_123])).
% 3.99/1.76  tff(c_239, plain, (![A_73, B_74, A_75]: (~r2_hidden('#skF_1'(A_73, B_74), A_75) | k4_xboole_0(A_75, B_74)!=A_75 | r1_xboole_0(A_73, B_74))), inference(resolution, [status(thm)], [c_4, c_162])).
% 3.99/1.76  tff(c_253, plain, (![B_2, A_1]: (k4_xboole_0(B_2, B_2)!=B_2 | r1_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_4, c_239])).
% 3.99/1.76  tff(c_260, plain, (![B_76, A_77]: (k1_xboole_0!=B_76 | r1_xboole_0(A_77, B_76))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_253])).
% 3.99/1.76  tff(c_2, plain, (![A_1, B_2, C_5]: (~r1_xboole_0(A_1, B_2) | ~r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.99/1.76  tff(c_356, plain, (![C_84, B_85, A_86]: (~r2_hidden(C_84, B_85) | ~r2_hidden(C_84, A_86) | k1_xboole_0!=B_85)), inference(resolution, [status(thm)], [c_260, c_2])).
% 3.99/1.76  tff(c_3780, plain, (![A_216, C_217, A_218]: (~r2_hidden('#skF_6'(A_216, k3_tarski(A_216), C_217), A_218) | k1_xboole_0!=A_216 | ~r2_hidden(C_217, k3_tarski(A_216)))), inference(resolution, [status(thm)], [c_22, c_356])).
% 3.99/1.76  tff(c_3806, plain, (![A_219, C_220]: (k1_xboole_0!=A_219 | ~r2_hidden(C_220, k3_tarski(A_219)))), inference(resolution, [status(thm)], [c_22, c_3780])).
% 3.99/1.76  tff(c_3859, plain, (k3_tarski(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_3806])).
% 3.99/1.76  tff(c_38, plain, (k3_tarski(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.99/1.76  tff(c_3862, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3859, c_38])).
% 3.99/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.99/1.76  
% 3.99/1.76  Inference rules
% 3.99/1.76  ----------------------
% 3.99/1.76  #Ref     : 0
% 3.99/1.76  #Sup     : 932
% 3.99/1.76  #Fact    : 0
% 3.99/1.76  #Define  : 0
% 3.99/1.76  #Split   : 0
% 3.99/1.76  #Chain   : 0
% 3.99/1.76  #Close   : 0
% 3.99/1.76  
% 3.99/1.76  Ordering : KBO
% 3.99/1.76  
% 3.99/1.76  Simplification rules
% 3.99/1.76  ----------------------
% 3.99/1.76  #Subsume      : 239
% 3.99/1.76  #Demod        : 529
% 3.99/1.76  #Tautology    : 417
% 3.99/1.76  #SimpNegUnit  : 0
% 3.99/1.76  #BackRed      : 1
% 3.99/1.76  
% 3.99/1.76  #Partial instantiations: 0
% 3.99/1.76  #Strategies tried      : 1
% 3.99/1.76  
% 3.99/1.76  Timing (in seconds)
% 3.99/1.76  ----------------------
% 3.99/1.76  Preprocessing        : 0.28
% 3.99/1.76  Parsing              : 0.16
% 3.99/1.76  CNF conversion       : 0.02
% 3.99/1.76  Main loop            : 0.72
% 3.99/1.76  Inferencing          : 0.26
% 3.99/1.76  Reduction            : 0.22
% 3.99/1.76  Demodulation         : 0.16
% 3.99/1.76  BG Simplification    : 0.03
% 3.99/1.76  Subsumption          : 0.17
% 3.99/1.76  Abstraction          : 0.05
% 3.99/1.76  MUC search           : 0.00
% 3.99/1.76  Cooper               : 0.00
% 3.99/1.76  Total                : 1.03
% 3.99/1.76  Index Insertion      : 0.00
% 3.99/1.76  Index Deletion       : 0.00
% 3.99/1.76  Index Matching       : 0.00
% 3.99/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
