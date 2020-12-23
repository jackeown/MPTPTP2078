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
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   16 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  23 expanded)
%              Number of equality atoms :    4 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff(k1_ordinal1,type,(
    k1_ordinal1: $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_46,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_49,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [A_14,B_15] :
      ( r2_hidden(A_14,B_15)
      | ~ r1_tarski(k1_tarski(A_14),B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_49,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(resolution,[status(thm)],[c_24,c_44])).

tff(c_30,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_tarski(A_11)) = k1_ordinal1(A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_56,plain,(
    ! [D_19,B_20,A_21] :
      ( ~ r2_hidden(D_19,B_20)
      | r2_hidden(D_19,k2_xboole_0(A_21,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_91,plain,(
    ! [D_32,A_33] :
      ( ~ r2_hidden(D_32,k1_tarski(A_33))
      | r2_hidden(D_32,k1_ordinal1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_95,plain,(
    ! [A_14] : r2_hidden(A_14,k1_ordinal1(A_14)) ),
    inference(resolution,[status(thm)],[c_49,c_91])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_3',k1_ordinal1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.18  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_2
% 1.80/1.18  
% 1.80/1.18  %Foreground sorts:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Background operators:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Foreground operators:
% 1.80/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.18  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.18  
% 1.80/1.19  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.19  tff(f_44, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.80/1.19  tff(f_46, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 1.80/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.80/1.19  tff(f_49, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 1.80/1.19  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.80/1.19  tff(c_44, plain, (![A_14, B_15]: (r2_hidden(A_14, B_15) | ~r1_tarski(k1_tarski(A_14), B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.80/1.19  tff(c_49, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(resolution, [status(thm)], [c_24, c_44])).
% 1.80/1.19  tff(c_30, plain, (![A_11]: (k2_xboole_0(A_11, k1_tarski(A_11))=k1_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.80/1.19  tff(c_56, plain, (![D_19, B_20, A_21]: (~r2_hidden(D_19, B_20) | r2_hidden(D_19, k2_xboole_0(A_21, B_20)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.80/1.19  tff(c_91, plain, (![D_32, A_33]: (~r2_hidden(D_32, k1_tarski(A_33)) | r2_hidden(D_32, k1_ordinal1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_56])).
% 1.80/1.19  tff(c_95, plain, (![A_14]: (r2_hidden(A_14, k1_ordinal1(A_14)))), inference(resolution, [status(thm)], [c_49, c_91])).
% 1.80/1.19  tff(c_32, plain, (~r2_hidden('#skF_3', k1_ordinal1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.80/1.19  tff(c_98, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_32])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 0
% 1.80/1.19  #Sup     : 13
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 0
% 1.80/1.19  #Chain   : 0
% 1.80/1.19  #Close   : 0
% 1.80/1.19  
% 1.80/1.19  Ordering : KBO
% 1.80/1.19  
% 1.80/1.19  Simplification rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Subsume      : 0
% 1.80/1.19  #Demod        : 3
% 1.80/1.19  #Tautology    : 7
% 1.80/1.19  #SimpNegUnit  : 0
% 1.80/1.19  #BackRed      : 1
% 1.80/1.19  
% 1.80/1.19  #Partial instantiations: 0
% 1.80/1.19  #Strategies tried      : 1
% 1.80/1.19  
% 1.80/1.19  Timing (in seconds)
% 1.80/1.19  ----------------------
% 1.80/1.19  Preprocessing        : 0.27
% 1.80/1.19  Parsing              : 0.15
% 1.80/1.19  CNF conversion       : 0.02
% 1.80/1.19  Main loop            : 0.12
% 1.80/1.19  Inferencing          : 0.05
% 1.80/1.19  Reduction            : 0.03
% 1.80/1.19  Demodulation         : 0.02
% 1.80/1.19  BG Simplification    : 0.01
% 1.80/1.19  Subsumption          : 0.03
% 1.80/1.19  Abstraction          : 0.01
% 1.80/1.19  MUC search           : 0.00
% 1.80/1.19  Cooper               : 0.00
% 1.80/1.19  Total                : 0.41
% 1.80/1.19  Index Insertion      : 0.00
% 1.80/1.19  Index Deletion       : 0.00
% 1.80/1.19  Index Matching       : 0.00
% 1.80/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
