%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:55 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   20 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  28 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_94,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_97,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_34,plain,(
    ! [A_32] : k2_xboole_0(A_32,k1_tarski(A_32)) = k1_ordinal1(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_48,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_100,plain,(
    ! [A_41,B_42] : r1_tarski(A_41,k2_xboole_0(B_42,A_41)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10])).

tff(c_103,plain,(
    ! [A_32] : r1_tarski(k1_tarski(A_32),k1_ordinal1(A_32)) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_100])).

tff(c_113,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(k1_tarski(A_43),B_44)
      | r2_hidden(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [B_28] : ~ r1_xboole_0(k1_tarski(B_28),k1_tarski(B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_118,plain,(
    ! [A_43] : r2_hidden(A_43,k1_tarski(A_43)) ),
    inference(resolution,[status(thm)],[c_113,c_26])).

tff(c_130,plain,(
    ! [C_55,B_56,A_57] :
      ( r2_hidden(C_55,B_56)
      | ~ r2_hidden(C_55,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_137,plain,(
    ! [A_58,B_59] :
      ( r2_hidden(A_58,B_59)
      | ~ r1_tarski(k1_tarski(A_58),B_59) ) ),
    inference(resolution,[status(thm)],[c_118,c_130])).

tff(c_159,plain,(
    ! [A_32] : r2_hidden(A_32,k1_ordinal1(A_32)) ),
    inference(resolution,[status(thm)],[c_103,c_137])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_2',k1_ordinal1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:40:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_2 > #skF_1
% 1.88/1.17  
% 1.88/1.17  %Foreground sorts:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Background operators:
% 1.88/1.17  
% 1.88/1.17  
% 1.88/1.17  %Foreground operators:
% 1.88/1.17  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.88/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.88/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.88/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.88/1.17  
% 1.88/1.18  tff(f_94, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.88/1.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.88/1.18  tff(f_36, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.88/1.18  tff(f_59, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.88/1.18  tff(f_84, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.88/1.18  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.88/1.18  tff(f_97, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.88/1.18  tff(c_34, plain, (![A_32]: (k2_xboole_0(A_32, k1_tarski(A_32))=k1_ordinal1(A_32))), inference(cnfTransformation, [status(thm)], [f_94])).
% 1.88/1.18  tff(c_48, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.18  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.88/1.18  tff(c_100, plain, (![A_41, B_42]: (r1_tarski(A_41, k2_xboole_0(B_42, A_41)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10])).
% 1.88/1.18  tff(c_103, plain, (![A_32]: (r1_tarski(k1_tarski(A_32), k1_ordinal1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_100])).
% 1.88/1.18  tff(c_113, plain, (![A_43, B_44]: (r1_xboole_0(k1_tarski(A_43), B_44) | r2_hidden(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.18  tff(c_26, plain, (![B_28]: (~r1_xboole_0(k1_tarski(B_28), k1_tarski(B_28)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 1.88/1.18  tff(c_118, plain, (![A_43]: (r2_hidden(A_43, k1_tarski(A_43)))), inference(resolution, [status(thm)], [c_113, c_26])).
% 1.88/1.18  tff(c_130, plain, (![C_55, B_56, A_57]: (r2_hidden(C_55, B_56) | ~r2_hidden(C_55, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.88/1.18  tff(c_137, plain, (![A_58, B_59]: (r2_hidden(A_58, B_59) | ~r1_tarski(k1_tarski(A_58), B_59))), inference(resolution, [status(thm)], [c_118, c_130])).
% 1.88/1.18  tff(c_159, plain, (![A_32]: (r2_hidden(A_32, k1_ordinal1(A_32)))), inference(resolution, [status(thm)], [c_103, c_137])).
% 1.88/1.18  tff(c_36, plain, (~r2_hidden('#skF_2', k1_ordinal1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_97])).
% 1.88/1.18  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_159, c_36])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 27
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 0
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 0
% 1.88/1.18  #Demod        : 5
% 1.88/1.18  #Tautology    : 16
% 1.88/1.18  #SimpNegUnit  : 0
% 1.88/1.18  #BackRed      : 1
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.18  Preprocessing        : 0.30
% 1.88/1.18  Parsing              : 0.17
% 1.88/1.18  CNF conversion       : 0.02
% 1.88/1.18  Main loop            : 0.12
% 1.88/1.18  Inferencing          : 0.04
% 1.88/1.18  Reduction            : 0.04
% 1.88/1.18  Demodulation         : 0.03
% 1.88/1.18  BG Simplification    : 0.01
% 1.88/1.18  Subsumption          : 0.02
% 1.88/1.18  Abstraction          : 0.01
% 1.88/1.18  MUC search           : 0.00
% 1.88/1.18  Cooper               : 0.00
% 1.88/1.18  Total                : 0.45
% 1.88/1.18  Index Insertion      : 0.00
% 1.88/1.18  Index Deletion       : 0.00
% 1.88/1.18  Index Matching       : 0.00
% 1.88/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
