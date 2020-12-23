%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   46 (  77 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 ( 103 expanded)
%              Number of equality atoms :   20 (  50 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_88,plain,(
    ! [A_44,B_45] : k1_enumset1(A_44,A_44,B_45) = k2_tarski(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_94,plain,(
    ! [B_45,A_44] : r2_hidden(B_45,k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_24])).

tff(c_68,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( k3_xboole_0(A_46,B_47) = A_46
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_110,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_9')) = k2_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_68,c_106])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k3_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [D_61] :
      ( r2_hidden(D_61,k1_tarski('#skF_9'))
      | ~ r2_hidden(D_61,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_4])).

tff(c_153,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_94,c_143])).

tff(c_46,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_161,plain,(
    '#skF_9' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_153,c_46])).

tff(c_58,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [E_15,B_10,C_11] : r2_hidden(E_15,k1_enumset1(E_15,B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [A_44,B_45] : r2_hidden(A_44,k2_tarski(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_28])).

tff(c_152,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_9')) ),
    inference(resolution,[status(thm)],[c_100,c_143])).

tff(c_157,plain,(
    '#skF_7' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_152,c_46])).

tff(c_66,plain,(
    k2_tarski('#skF_7','#skF_8') != k1_tarski('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_166,plain,(
    k2_tarski('#skF_9','#skF_8') != k1_tarski('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_66])).

tff(c_184,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_58,c_161,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.31  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.17/1.31  
% 2.17/1.31  %Foreground sorts:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Background operators:
% 2.17/1.31  
% 2.17/1.31  
% 2.17/1.31  %Foreground operators:
% 2.17/1.31  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.17/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.17/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.17/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.31  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.17/1.31  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.17/1.31  
% 2.17/1.32  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.17/1.32  tff(f_53, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.17/1.32  tff(f_73, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.17/1.32  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.32  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.17/1.32  tff(f_60, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.17/1.32  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.32  tff(c_88, plain, (![A_44, B_45]: (k1_enumset1(A_44, A_44, B_45)=k2_tarski(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.17/1.32  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.32  tff(c_94, plain, (![B_45, A_44]: (r2_hidden(B_45, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_24])).
% 2.17/1.32  tff(c_68, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.32  tff(c_106, plain, (![A_46, B_47]: (k3_xboole_0(A_46, B_47)=A_46 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.32  tff(c_110, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_9'))=k2_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_68, c_106])).
% 2.17/1.32  tff(c_4, plain, (![D_6, B_2, A_1]: (r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k3_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.17/1.32  tff(c_143, plain, (![D_61]: (r2_hidden(D_61, k1_tarski('#skF_9')) | ~r2_hidden(D_61, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_110, c_4])).
% 2.17/1.32  tff(c_153, plain, (r2_hidden('#skF_8', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_94, c_143])).
% 2.17/1.32  tff(c_46, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.32  tff(c_161, plain, ('#skF_9'='#skF_8'), inference(resolution, [status(thm)], [c_153, c_46])).
% 2.17/1.32  tff(c_58, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.32  tff(c_28, plain, (![E_15, B_10, C_11]: (r2_hidden(E_15, k1_enumset1(E_15, B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.32  tff(c_100, plain, (![A_44, B_45]: (r2_hidden(A_44, k2_tarski(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_28])).
% 2.17/1.32  tff(c_152, plain, (r2_hidden('#skF_7', k1_tarski('#skF_9'))), inference(resolution, [status(thm)], [c_100, c_143])).
% 2.17/1.32  tff(c_157, plain, ('#skF_7'='#skF_9'), inference(resolution, [status(thm)], [c_152, c_46])).
% 2.17/1.32  tff(c_66, plain, (k2_tarski('#skF_7', '#skF_8')!=k1_tarski('#skF_9')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.17/1.32  tff(c_166, plain, (k2_tarski('#skF_9', '#skF_8')!=k1_tarski('#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_66])).
% 2.17/1.32  tff(c_184, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_161, c_58, c_161, c_166])).
% 2.17/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  Inference rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Ref     : 0
% 2.17/1.32  #Sup     : 27
% 2.17/1.32  #Fact    : 0
% 2.17/1.32  #Define  : 0
% 2.17/1.32  #Split   : 0
% 2.17/1.32  #Chain   : 0
% 2.17/1.32  #Close   : 0
% 2.17/1.32  
% 2.17/1.32  Ordering : KBO
% 2.17/1.32  
% 2.17/1.32  Simplification rules
% 2.17/1.32  ----------------------
% 2.17/1.32  #Subsume      : 0
% 2.17/1.32  #Demod        : 16
% 2.17/1.32  #Tautology    : 21
% 2.17/1.32  #SimpNegUnit  : 0
% 2.17/1.32  #BackRed      : 7
% 2.17/1.32  
% 2.17/1.32  #Partial instantiations: 0
% 2.17/1.32  #Strategies tried      : 1
% 2.17/1.32  
% 2.17/1.32  Timing (in seconds)
% 2.17/1.32  ----------------------
% 2.17/1.32  Preprocessing        : 0.34
% 2.17/1.32  Parsing              : 0.17
% 2.17/1.32  CNF conversion       : 0.03
% 2.17/1.32  Main loop            : 0.15
% 2.17/1.32  Inferencing          : 0.04
% 2.17/1.32  Reduction            : 0.06
% 2.17/1.32  Demodulation         : 0.04
% 2.17/1.32  BG Simplification    : 0.02
% 2.17/1.32  Subsumption          : 0.03
% 2.17/1.32  Abstraction          : 0.01
% 2.17/1.32  MUC search           : 0.00
% 2.17/1.32  Cooper               : 0.00
% 2.17/1.32  Total                : 0.52
% 2.17/1.32  Index Insertion      : 0.00
% 2.17/1.32  Index Deletion       : 0.00
% 2.17/1.32  Index Matching       : 0.00
% 2.17/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
