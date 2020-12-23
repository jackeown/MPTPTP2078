%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:47 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   42 (  46 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  47 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_17,B_18] : k2_xboole_0(A_17,k4_xboole_0(B_18,A_17)) = k2_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_27,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_30,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_20,c_27])).

tff(c_205,plain,(
    ! [A_58,B_59] : k2_xboole_0(k5_xboole_0(A_58,B_59),k3_xboole_0(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_81,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_1'(A_40,B_41),A_40)
      | r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_10,B_11,C_14] :
      ( ~ r1_xboole_0(A_10,B_11)
      | ~ r2_hidden(C_14,k3_xboole_0(A_10,B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_106,plain,(
    ! [A_44,B_45,B_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | r1_tarski(k3_xboole_0(A_44,B_45),B_46) ) ),
    inference(resolution,[status(thm)],[c_81,c_14])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_115,plain,(
    ! [A_50,B_51,B_52] :
      ( k2_xboole_0(k3_xboole_0(A_50,B_51),B_52) = B_52
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(resolution,[status(thm)],[c_106,c_16])).

tff(c_129,plain,(
    ! [B_52,A_50,B_51] :
      ( k2_xboole_0(B_52,k3_xboole_0(A_50,B_51)) = B_52
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_2])).

tff(c_233,plain,(
    ! [A_60,B_61] :
      ( k5_xboole_0(A_60,B_61) = k2_xboole_0(A_60,B_61)
      | ~ r1_xboole_0(A_60,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_205,c_129])).

tff(c_236,plain,(
    ! [B_20,A_19] : k5_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k2_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_30,c_233])).

tff(c_241,plain,(
    ! [B_20,A_19] : k5_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k2_xboole_0(B_20,A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_236])).

tff(c_24,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_3')) != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_25,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_3')) != k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_244,plain,(
    k2_xboole_0('#skF_3','#skF_4') != k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_241,c_25])).

tff(c_247,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_244])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n010.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:24:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.87/1.21  
% 1.87/1.21  %Foreground sorts:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Background operators:
% 1.87/1.21  
% 1.87/1.21  
% 1.87/1.21  %Foreground operators:
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.87/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.87/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.21  
% 1.87/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.87/1.22  tff(f_58, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.87/1.22  tff(f_60, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.87/1.22  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.87/1.22  tff(f_62, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_xboole_1)).
% 1.87/1.22  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.87/1.22  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.87/1.22  tff(f_56, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.22  tff(f_65, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.87/1.22  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.22  tff(c_18, plain, (![A_17, B_18]: (k2_xboole_0(A_17, k4_xboole_0(B_18, A_17))=k2_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.87/1.22  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.87/1.22  tff(c_27, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.22  tff(c_30, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_20, c_27])).
% 1.87/1.22  tff(c_205, plain, (![A_58, B_59]: (k2_xboole_0(k5_xboole_0(A_58, B_59), k3_xboole_0(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.87/1.22  tff(c_81, plain, (![A_40, B_41]: (r2_hidden('#skF_1'(A_40, B_41), A_40) | r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.22  tff(c_14, plain, (![A_10, B_11, C_14]: (~r1_xboole_0(A_10, B_11) | ~r2_hidden(C_14, k3_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.87/1.22  tff(c_106, plain, (![A_44, B_45, B_46]: (~r1_xboole_0(A_44, B_45) | r1_tarski(k3_xboole_0(A_44, B_45), B_46))), inference(resolution, [status(thm)], [c_81, c_14])).
% 1.87/1.22  tff(c_16, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.22  tff(c_115, plain, (![A_50, B_51, B_52]: (k2_xboole_0(k3_xboole_0(A_50, B_51), B_52)=B_52 | ~r1_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_106, c_16])).
% 1.87/1.22  tff(c_129, plain, (![B_52, A_50, B_51]: (k2_xboole_0(B_52, k3_xboole_0(A_50, B_51))=B_52 | ~r1_xboole_0(A_50, B_51))), inference(superposition, [status(thm), theory('equality')], [c_115, c_2])).
% 1.87/1.22  tff(c_233, plain, (![A_60, B_61]: (k5_xboole_0(A_60, B_61)=k2_xboole_0(A_60, B_61) | ~r1_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_205, c_129])).
% 1.87/1.22  tff(c_236, plain, (![B_20, A_19]: (k5_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k2_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_30, c_233])).
% 1.87/1.22  tff(c_241, plain, (![B_20, A_19]: (k5_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k2_xboole_0(B_20, A_19))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_236])).
% 1.87/1.22  tff(c_24, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.22  tff(c_25, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))!=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_24])).
% 1.87/1.22  tff(c_244, plain, (k2_xboole_0('#skF_3', '#skF_4')!=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_241, c_25])).
% 1.87/1.22  tff(c_247, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_244])).
% 1.87/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.22  
% 1.87/1.22  Inference rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Ref     : 0
% 1.87/1.22  #Sup     : 51
% 1.87/1.22  #Fact    : 0
% 1.87/1.22  #Define  : 0
% 1.87/1.22  #Split   : 0
% 1.87/1.22  #Chain   : 0
% 1.87/1.22  #Close   : 0
% 1.87/1.22  
% 1.87/1.22  Ordering : KBO
% 1.87/1.22  
% 1.87/1.22  Simplification rules
% 1.87/1.22  ----------------------
% 1.87/1.22  #Subsume      : 7
% 1.87/1.22  #Demod        : 7
% 1.87/1.22  #Tautology    : 24
% 1.87/1.22  #SimpNegUnit  : 0
% 1.87/1.22  #BackRed      : 1
% 1.87/1.22  
% 1.87/1.22  #Partial instantiations: 0
% 1.87/1.22  #Strategies tried      : 1
% 1.87/1.22  
% 1.87/1.22  Timing (in seconds)
% 1.87/1.22  ----------------------
% 1.87/1.22  Preprocessing        : 0.26
% 1.87/1.22  Parsing              : 0.14
% 1.87/1.22  CNF conversion       : 0.02
% 1.87/1.22  Main loop            : 0.17
% 1.87/1.22  Inferencing          : 0.06
% 1.87/1.22  Reduction            : 0.06
% 1.87/1.22  Demodulation         : 0.05
% 1.87/1.22  BG Simplification    : 0.01
% 1.87/1.22  Subsumption          : 0.03
% 1.87/1.22  Abstraction          : 0.01
% 1.87/1.22  MUC search           : 0.00
% 1.87/1.22  Cooper               : 0.00
% 1.87/1.22  Total                : 0.46
% 1.87/1.22  Index Insertion      : 0.00
% 1.87/1.22  Index Deletion       : 0.00
% 1.87/1.22  Index Matching       : 0.00
% 1.87/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
