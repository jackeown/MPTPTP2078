%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:44 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_49,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_56,plain,(
    ! [D_19,B_20] : r2_hidden(D_19,k2_tarski(D_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_59,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_56])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_46,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    ! [A_24,B_25] :
      ( k2_xboole_0(A_24,B_25) = B_25
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_70,plain,(
    k2_xboole_0(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_46,c_66])).

tff(c_88,plain,(
    ! [D_31,A_32,B_33] :
      ( ~ r2_hidden(D_31,A_32)
      | r2_hidden(D_31,k2_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_112,plain,(
    ! [D_39] :
      ( ~ r2_hidden(D_39,k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'))
      | r2_hidden(D_39,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_88])).

tff(c_123,plain,(
    ! [D_40] :
      ( r2_hidden(D_40,'#skF_6')
      | ~ r2_hidden(D_40,k1_tarski('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_6,c_112])).

tff(c_127,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_59,c_123])).

tff(c_131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:18:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  
% 1.78/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.17  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.78/1.17  
% 1.78/1.17  %Foreground sorts:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Background operators:
% 1.78/1.17  
% 1.78/1.17  
% 1.78/1.17  %Foreground operators:
% 1.78/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.78/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.78/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.78/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.78/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.78/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.78/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.17  
% 1.87/1.18  tff(f_56, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 1.87/1.18  tff(f_49, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.87/1.18  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.87/1.18  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.87/1.18  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.18  tff(c_44, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.18  tff(c_56, plain, (![D_19, B_20]: (r2_hidden(D_19, k2_tarski(D_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.87/1.18  tff(c_59, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_56])).
% 1.87/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.18  tff(c_46, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.87/1.18  tff(c_66, plain, (![A_24, B_25]: (k2_xboole_0(A_24, B_25)=B_25 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.87/1.18  tff(c_70, plain, (k2_xboole_0(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')='#skF_6'), inference(resolution, [status(thm)], [c_46, c_66])).
% 1.87/1.18  tff(c_88, plain, (![D_31, A_32, B_33]: (~r2_hidden(D_31, A_32) | r2_hidden(D_31, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.18  tff(c_112, plain, (![D_39]: (~r2_hidden(D_39, k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')) | r2_hidden(D_39, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_88])).
% 1.87/1.18  tff(c_123, plain, (![D_40]: (r2_hidden(D_40, '#skF_6') | ~r2_hidden(D_40, k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_6, c_112])).
% 1.87/1.18  tff(c_127, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_59, c_123])).
% 1.87/1.18  tff(c_131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_127])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 18
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 0
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Subsume      : 0
% 1.87/1.18  #Demod        : 1
% 1.87/1.18  #Tautology    : 12
% 1.87/1.18  #SimpNegUnit  : 1
% 1.87/1.18  #BackRed      : 0
% 1.87/1.18  
% 1.87/1.18  #Partial instantiations: 0
% 1.87/1.18  #Strategies tried      : 1
% 1.87/1.18  
% 1.87/1.18  Timing (in seconds)
% 1.87/1.18  ----------------------
% 1.87/1.18  Preprocessing        : 0.30
% 1.87/1.18  Parsing              : 0.15
% 1.87/1.18  CNF conversion       : 0.02
% 1.87/1.18  Main loop            : 0.12
% 1.87/1.18  Inferencing          : 0.04
% 1.87/1.18  Reduction            : 0.04
% 1.87/1.18  Demodulation         : 0.03
% 1.87/1.18  BG Simplification    : 0.01
% 1.87/1.18  Subsumption          : 0.02
% 1.87/1.18  Abstraction          : 0.01
% 1.87/1.18  MUC search           : 0.00
% 1.87/1.18  Cooper               : 0.00
% 1.87/1.18  Total                : 0.45
% 1.87/1.18  Index Insertion      : 0.00
% 1.87/1.18  Index Deletion       : 0.00
% 1.87/1.18  Index Matching       : 0.00
% 1.87/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
