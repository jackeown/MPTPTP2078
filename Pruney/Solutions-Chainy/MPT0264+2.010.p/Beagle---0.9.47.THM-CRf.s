%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:22 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   15 (  19 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5

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

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_62,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_64,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_135,plain,(
    ! [A_39,B_40] : k1_enumset1(A_39,A_39,B_40) = k2_tarski(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [E_15,A_9,B_10] : r2_hidden(E_15,k1_enumset1(A_9,B_10,E_15)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_144,plain,(
    ! [B_40,A_39] : r2_hidden(B_40,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_24])).

tff(c_66,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_204,plain,(
    ! [D_53,A_54,B_55] :
      ( r2_hidden(D_53,k3_xboole_0(A_54,B_55))
      | ~ r2_hidden(D_53,B_55)
      | ~ r2_hidden(D_53,A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_271,plain,(
    ! [D_64] :
      ( r2_hidden(D_64,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_64,'#skF_9')
      | ~ r2_hidden(D_64,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_204])).

tff(c_282,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_144,c_271])).

tff(c_291,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_282])).

tff(c_46,plain,(
    ! [C_20,A_16] :
      ( C_20 = A_16
      | ~ r2_hidden(C_20,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_300,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_291,c_46])).

tff(c_306,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_300])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:49:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  
% 2.11/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.25  %$ r2_hidden > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_6 > #skF_1 > #skF_7 > #skF_2 > #skF_9 > #skF_4 > #skF_8 > #skF_3 > #skF_5
% 2.11/1.25  
% 2.11/1.25  %Foreground sorts:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Background operators:
% 2.11/1.25  
% 2.11/1.25  
% 2.11/1.25  %Foreground operators:
% 2.11/1.25  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.11/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.25  tff('#skF_7', type, '#skF_7': $i).
% 2.11/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_9', type, '#skF_9': $i).
% 2.11/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_8', type, '#skF_8': $i).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.11/1.25  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.11/1.25  
% 2.11/1.26  tff(f_71, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.11/1.26  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.11/1.26  tff(f_51, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.11/1.26  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.11/1.26  tff(f_58, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.11/1.26  tff(c_62, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.26  tff(c_64, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.26  tff(c_135, plain, (![A_39, B_40]: (k1_enumset1(A_39, A_39, B_40)=k2_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.11/1.26  tff(c_24, plain, (![E_15, A_9, B_10]: (r2_hidden(E_15, k1_enumset1(A_9, B_10, E_15)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.11/1.26  tff(c_144, plain, (![B_40, A_39]: (r2_hidden(B_40, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_24])).
% 2.11/1.26  tff(c_66, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.11/1.26  tff(c_204, plain, (![D_53, A_54, B_55]: (r2_hidden(D_53, k3_xboole_0(A_54, B_55)) | ~r2_hidden(D_53, B_55) | ~r2_hidden(D_53, A_54))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.11/1.26  tff(c_271, plain, (![D_64]: (r2_hidden(D_64, k1_tarski('#skF_7')) | ~r2_hidden(D_64, '#skF_9') | ~r2_hidden(D_64, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_204])).
% 2.11/1.26  tff(c_282, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_144, c_271])).
% 2.11/1.26  tff(c_291, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_282])).
% 2.11/1.26  tff(c_46, plain, (![C_20, A_16]: (C_20=A_16 | ~r2_hidden(C_20, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.11/1.26  tff(c_300, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_291, c_46])).
% 2.11/1.26  tff(c_306, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_300])).
% 2.11/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.26  
% 2.11/1.26  Inference rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Ref     : 0
% 2.11/1.26  #Sup     : 56
% 2.11/1.26  #Fact    : 0
% 2.11/1.26  #Define  : 0
% 2.11/1.26  #Split   : 0
% 2.11/1.26  #Chain   : 0
% 2.11/1.26  #Close   : 0
% 2.11/1.26  
% 2.11/1.26  Ordering : KBO
% 2.11/1.26  
% 2.11/1.26  Simplification rules
% 2.11/1.26  ----------------------
% 2.11/1.26  #Subsume      : 8
% 2.11/1.26  #Demod        : 10
% 2.11/1.26  #Tautology    : 31
% 2.11/1.26  #SimpNegUnit  : 1
% 2.11/1.26  #BackRed      : 0
% 2.11/1.26  
% 2.11/1.26  #Partial instantiations: 0
% 2.11/1.26  #Strategies tried      : 1
% 2.11/1.26  
% 2.11/1.26  Timing (in seconds)
% 2.11/1.26  ----------------------
% 2.11/1.26  Preprocessing        : 0.30
% 2.11/1.26  Parsing              : 0.14
% 2.11/1.26  CNF conversion       : 0.02
% 2.11/1.26  Main loop            : 0.21
% 2.11/1.26  Inferencing          : 0.07
% 2.11/1.26  Reduction            : 0.08
% 2.11/1.26  Demodulation         : 0.06
% 2.11/1.26  BG Simplification    : 0.01
% 2.11/1.27  Subsumption          : 0.04
% 2.11/1.27  Abstraction          : 0.01
% 2.11/1.27  MUC search           : 0.00
% 2.11/1.27  Cooper               : 0.00
% 2.11/1.27  Total                : 0.53
% 2.11/1.27  Index Insertion      : 0.00
% 2.11/1.27  Index Deletion       : 0.00
% 2.11/1.27  Index Matching       : 0.00
% 2.11/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
