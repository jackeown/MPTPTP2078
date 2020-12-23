%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:56 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   35 (  35 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(f_60,axiom,(
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

tff(f_63,negated_conjecture,(
    ~ ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_104,plain,(
    ! [A_52,B_53,C_54] : k2_enumset1(A_52,A_52,B_53,C_54) = k1_enumset1(A_52,B_53,C_54) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_32,plain,(
    ! [F_20,A_13,C_15,D_16] : r2_hidden(F_20,k2_enumset1(A_13,F_20,C_15,D_16)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_125,plain,(
    ! [A_55,B_56,C_57] : r2_hidden(A_55,k1_enumset1(A_55,B_56,C_57)) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_32])).

tff(c_141,plain,(
    ! [A_61,B_62] : r2_hidden(A_61,k2_tarski(A_61,B_62)) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_125])).

tff(c_145,plain,(
    ! [A_63] : r2_hidden(A_63,k1_tarski(A_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_141])).

tff(c_56,plain,(
    ! [A_21] : k2_xboole_0(A_21,k1_tarski(A_21)) = k1_ordinal1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_90,plain,(
    ! [D_42,B_43,A_44] :
      ( ~ r2_hidden(D_42,B_43)
      | r2_hidden(D_42,k2_xboole_0(A_44,B_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_93,plain,(
    ! [D_42,A_21] :
      ( ~ r2_hidden(D_42,k1_tarski(A_21))
      | r2_hidden(D_42,k1_ordinal1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_90])).

tff(c_149,plain,(
    ! [A_63] : r2_hidden(A_63,k1_ordinal1(A_63)) ),
    inference(resolution,[status(thm)],[c_145,c_93])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5',k1_ordinal1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_152,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_58])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  
% 2.03/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.25  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_2 > #skF_3
% 2.03/1.25  
% 2.03/1.25  %Foreground sorts:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Background operators:
% 2.03/1.25  
% 2.03/1.25  
% 2.03/1.25  %Foreground operators:
% 2.03/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.03/1.25  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.03/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.03/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.03/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.03/1.25  tff('#skF_5', type, '#skF_5': $i).
% 2.03/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.03/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.03/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.25  
% 2.03/1.26  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.03/1.26  tff(f_38, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.03/1.26  tff(f_40, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.03/1.26  tff(f_58, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.03/1.26  tff(f_60, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 2.03/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.03/1.26  tff(f_63, negated_conjecture, ~(![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 2.03/1.26  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.03/1.26  tff(c_22, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.03/1.26  tff(c_104, plain, (![A_52, B_53, C_54]: (k2_enumset1(A_52, A_52, B_53, C_54)=k1_enumset1(A_52, B_53, C_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.03/1.26  tff(c_32, plain, (![F_20, A_13, C_15, D_16]: (r2_hidden(F_20, k2_enumset1(A_13, F_20, C_15, D_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.03/1.26  tff(c_125, plain, (![A_55, B_56, C_57]: (r2_hidden(A_55, k1_enumset1(A_55, B_56, C_57)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_32])).
% 2.03/1.26  tff(c_141, plain, (![A_61, B_62]: (r2_hidden(A_61, k2_tarski(A_61, B_62)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_125])).
% 2.03/1.26  tff(c_145, plain, (![A_63]: (r2_hidden(A_63, k1_tarski(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_141])).
% 2.03/1.26  tff(c_56, plain, (![A_21]: (k2_xboole_0(A_21, k1_tarski(A_21))=k1_ordinal1(A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.03/1.26  tff(c_90, plain, (![D_42, B_43, A_44]: (~r2_hidden(D_42, B_43) | r2_hidden(D_42, k2_xboole_0(A_44, B_43)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.03/1.26  tff(c_93, plain, (![D_42, A_21]: (~r2_hidden(D_42, k1_tarski(A_21)) | r2_hidden(D_42, k1_ordinal1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_90])).
% 2.03/1.26  tff(c_149, plain, (![A_63]: (r2_hidden(A_63, k1_ordinal1(A_63)))), inference(resolution, [status(thm)], [c_145, c_93])).
% 2.03/1.26  tff(c_58, plain, (~r2_hidden('#skF_5', k1_ordinal1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.03/1.26  tff(c_152, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_58])).
% 2.03/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.26  
% 2.03/1.26  Inference rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Ref     : 0
% 2.03/1.26  #Sup     : 21
% 2.03/1.26  #Fact    : 0
% 2.03/1.26  #Define  : 0
% 2.03/1.26  #Split   : 0
% 2.03/1.26  #Chain   : 0
% 2.03/1.26  #Close   : 0
% 2.03/1.26  
% 2.03/1.26  Ordering : KBO
% 2.03/1.26  
% 2.03/1.26  Simplification rules
% 2.03/1.26  ----------------------
% 2.03/1.26  #Subsume      : 0
% 2.03/1.26  #Demod        : 1
% 2.03/1.26  #Tautology    : 10
% 2.03/1.26  #SimpNegUnit  : 0
% 2.03/1.26  #BackRed      : 1
% 2.03/1.26  
% 2.03/1.26  #Partial instantiations: 0
% 2.03/1.26  #Strategies tried      : 1
% 2.03/1.26  
% 2.03/1.26  Timing (in seconds)
% 2.03/1.26  ----------------------
% 2.03/1.27  Preprocessing        : 0.30
% 2.03/1.27  Parsing              : 0.14
% 2.03/1.27  CNF conversion       : 0.02
% 2.03/1.27  Main loop            : 0.15
% 2.03/1.27  Inferencing          : 0.04
% 2.03/1.27  Reduction            : 0.05
% 2.03/1.27  Demodulation         : 0.04
% 2.03/1.27  BG Simplification    : 0.01
% 2.03/1.27  Subsumption          : 0.04
% 2.03/1.27  Abstraction          : 0.01
% 2.03/1.27  MUC search           : 0.00
% 2.03/1.27  Cooper               : 0.00
% 2.03/1.27  Total                : 0.48
% 2.03/1.27  Index Insertion      : 0.00
% 2.03/1.27  Index Deletion       : 0.00
% 2.03/1.27  Index Matching       : 0.00
% 2.03/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
