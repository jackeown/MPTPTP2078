%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  35 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_52,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_122,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(k1_tarski(A_38),B_39) = k1_tarski(A_38)
      | r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_88,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != A_30 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_96,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(resolution,[status(thm)],[c_88,c_28])).

tff(c_148,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_96])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(k1_tarski(A_15),B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_159,plain,(
    ! [A_43,B_44] :
      ( k3_xboole_0(k1_tarski(A_43),B_44) = k1_tarski(A_43)
      | ~ r2_hidden(A_43,B_44) ) ),
    inference(resolution,[status(thm)],[c_20,c_97])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_182,plain,(
    ! [B_45,A_46] :
      ( k3_xboole_0(B_45,k1_tarski(A_46)) = k1_tarski(A_46)
      | ~ r2_hidden(A_46,B_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_2])).

tff(c_26,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_29,plain,(
    k3_xboole_0('#skF_2',k1_tarski('#skF_1')) != k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_29])).

tff(c_218,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n013.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 12:52:24 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  
% 1.93/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 1.93/1.18  
% 1.93/1.18  %Foreground sorts:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Background operators:
% 1.93/1.18  
% 1.93/1.18  
% 1.93/1.18  %Foreground operators:
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.93/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.18  
% 1.93/1.19  tff(f_52, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 1.93/1.19  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.93/1.19  tff(f_57, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 1.93/1.19  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.93/1.19  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.93/1.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.93/1.19  tff(c_122, plain, (![A_38, B_39]: (k4_xboole_0(k1_tarski(A_38), B_39)=k1_tarski(A_38) | r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.93/1.19  tff(c_88, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k4_xboole_0(A_30, B_31)!=A_30)), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.93/1.19  tff(c_28, plain, (~r1_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.19  tff(c_96, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(resolution, [status(thm)], [c_88, c_28])).
% 1.93/1.19  tff(c_148, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_122, c_96])).
% 1.93/1.19  tff(c_20, plain, (![A_15, B_16]: (r1_tarski(k1_tarski(A_15), B_16) | ~r2_hidden(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.19  tff(c_97, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.19  tff(c_159, plain, (![A_43, B_44]: (k3_xboole_0(k1_tarski(A_43), B_44)=k1_tarski(A_43) | ~r2_hidden(A_43, B_44))), inference(resolution, [status(thm)], [c_20, c_97])).
% 1.93/1.19  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.19  tff(c_182, plain, (![B_45, A_46]: (k3_xboole_0(B_45, k1_tarski(A_46))=k1_tarski(A_46) | ~r2_hidden(A_46, B_45))), inference(superposition, [status(thm), theory('equality')], [c_159, c_2])).
% 1.93/1.19  tff(c_26, plain, (k3_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.19  tff(c_29, plain, (k3_xboole_0('#skF_2', k1_tarski('#skF_1'))!=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_26])).
% 1.93/1.19  tff(c_192, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_182, c_29])).
% 1.93/1.19  tff(c_218, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_148, c_192])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 45
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 0
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 0
% 1.93/1.19  #Demod        : 2
% 1.93/1.19  #Tautology    : 24
% 1.93/1.19  #SimpNegUnit  : 0
% 1.93/1.19  #BackRed      : 0
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.20  Preprocessing        : 0.29
% 1.93/1.20  Parsing              : 0.15
% 1.93/1.20  CNF conversion       : 0.02
% 1.93/1.20  Main loop            : 0.16
% 1.93/1.20  Inferencing          : 0.07
% 1.93/1.20  Reduction            : 0.04
% 1.93/1.20  Demodulation         : 0.03
% 1.93/1.20  BG Simplification    : 0.01
% 1.97/1.20  Subsumption          : 0.02
% 1.97/1.20  Abstraction          : 0.01
% 1.97/1.20  MUC search           : 0.00
% 1.97/1.20  Cooper               : 0.00
% 1.97/1.20  Total                : 0.47
% 1.97/1.20  Index Insertion      : 0.00
% 1.97/1.20  Index Deletion       : 0.00
% 1.97/1.20  Index Matching       : 0.00
% 1.97/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
