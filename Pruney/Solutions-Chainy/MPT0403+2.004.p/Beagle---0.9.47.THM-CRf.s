%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:41 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   45 (  68 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( C = k2_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k2_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_setfam_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_setfam_1(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_45,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_1'(A_58,B_59),B_59)
      | r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_51,plain,(
    ! [A_60] : r1_tarski(A_60,A_60) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_55,plain,(
    ! [A_60] : k2_xboole_0(A_60,A_60) = A_60 ),
    inference(resolution,[status(thm)],[c_51,c_8])).

tff(c_129,plain,(
    ! [E_90,F_91,A_92,B_93] :
      ( r2_hidden(k2_xboole_0(E_90,F_91),k2_setfam_1(A_92,B_93))
      | ~ r2_hidden(F_91,B_93)
      | ~ r2_hidden(E_90,A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_136,plain,(
    ! [A_94,A_95,B_96] :
      ( r2_hidden(A_94,k2_setfam_1(A_95,B_96))
      | ~ r2_hidden(A_94,B_96)
      | ~ r2_hidden(A_94,A_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55,c_129])).

tff(c_50,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_45])).

tff(c_73,plain,(
    ! [A_67,B_68,D_69] :
      ( ~ r1_tarski('#skF_2'(A_67,B_68),D_69)
      | ~ r2_hidden(D_69,B_68)
      | r1_setfam_1(A_67,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78,plain,(
    ! [A_67,B_68] :
      ( ~ r2_hidden('#skF_2'(A_67,B_68),B_68)
      | r1_setfam_1(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_50,c_73])).

tff(c_368,plain,(
    ! [A_210,A_211,B_212] :
      ( r1_setfam_1(A_210,k2_setfam_1(A_211,B_212))
      | ~ r2_hidden('#skF_2'(A_210,k2_setfam_1(A_211,B_212)),B_212)
      | ~ r2_hidden('#skF_2'(A_210,k2_setfam_1(A_211,B_212)),A_211) ) ),
    inference(resolution,[status(thm)],[c_136,c_78])).

tff(c_397,plain,(
    ! [A_216,A_217] :
      ( ~ r2_hidden('#skF_2'(A_216,k2_setfam_1(A_217,A_216)),A_217)
      | r1_setfam_1(A_216,k2_setfam_1(A_217,A_216)) ) ),
    inference(resolution,[status(thm)],[c_16,c_368])).

tff(c_412,plain,(
    ! [A_8] : r1_setfam_1(A_8,k2_setfam_1(A_8,A_8)) ),
    inference(resolution,[status(thm)],[c_16,c_397])).

tff(c_42,plain,(
    ~ r1_setfam_1('#skF_10',k2_setfam_1('#skF_10','#skF_10')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_415,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_412,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:48:02 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  
% 2.49/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.36  %$ r2_hidden > r1_tarski > r1_setfam_1 > k2_xboole_0 > k2_setfam_1 > #nlpp > #skF_6 > #skF_9 > #skF_4 > #skF_10 > #skF_8 > #skF_5 > #skF_7 > #skF_3 > #skF_2 > #skF_1
% 2.49/1.36  
% 2.49/1.36  %Foreground sorts:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Background operators:
% 2.49/1.36  
% 2.49/1.36  
% 2.49/1.36  %Foreground operators:
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.36  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.49/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.49/1.36  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_9', type, '#skF_9': ($i * $i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.49/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.36  tff('#skF_10', type, '#skF_10': $i).
% 2.49/1.36  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.49/1.36  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.36  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.49/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.36  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.49/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.49/1.36  
% 2.49/1.37  tff(f_48, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.49/1.37  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.49/1.37  tff(f_36, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.49/1.37  tff(f_60, axiom, (![A, B, C]: ((C = k2_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k2_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_setfam_1)).
% 2.49/1.37  tff(f_63, negated_conjecture, ~(![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 2.49/1.37  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_setfam_1(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.37  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.37  tff(c_45, plain, (![A_58, B_59]: (~r2_hidden('#skF_1'(A_58, B_59), B_59) | r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.49/1.37  tff(c_51, plain, (![A_60]: (r1_tarski(A_60, A_60))), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.49/1.37  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.49/1.37  tff(c_55, plain, (![A_60]: (k2_xboole_0(A_60, A_60)=A_60)), inference(resolution, [status(thm)], [c_51, c_8])).
% 2.49/1.37  tff(c_129, plain, (![E_90, F_91, A_92, B_93]: (r2_hidden(k2_xboole_0(E_90, F_91), k2_setfam_1(A_92, B_93)) | ~r2_hidden(F_91, B_93) | ~r2_hidden(E_90, A_92))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.49/1.37  tff(c_136, plain, (![A_94, A_95, B_96]: (r2_hidden(A_94, k2_setfam_1(A_95, B_96)) | ~r2_hidden(A_94, B_96) | ~r2_hidden(A_94, A_95))), inference(superposition, [status(thm), theory('equality')], [c_55, c_129])).
% 2.49/1.37  tff(c_50, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_45])).
% 2.49/1.37  tff(c_73, plain, (![A_67, B_68, D_69]: (~r1_tarski('#skF_2'(A_67, B_68), D_69) | ~r2_hidden(D_69, B_68) | r1_setfam_1(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.49/1.37  tff(c_78, plain, (![A_67, B_68]: (~r2_hidden('#skF_2'(A_67, B_68), B_68) | r1_setfam_1(A_67, B_68))), inference(resolution, [status(thm)], [c_50, c_73])).
% 2.49/1.37  tff(c_368, plain, (![A_210, A_211, B_212]: (r1_setfam_1(A_210, k2_setfam_1(A_211, B_212)) | ~r2_hidden('#skF_2'(A_210, k2_setfam_1(A_211, B_212)), B_212) | ~r2_hidden('#skF_2'(A_210, k2_setfam_1(A_211, B_212)), A_211))), inference(resolution, [status(thm)], [c_136, c_78])).
% 2.49/1.37  tff(c_397, plain, (![A_216, A_217]: (~r2_hidden('#skF_2'(A_216, k2_setfam_1(A_217, A_216)), A_217) | r1_setfam_1(A_216, k2_setfam_1(A_217, A_216)))), inference(resolution, [status(thm)], [c_16, c_368])).
% 2.49/1.37  tff(c_412, plain, (![A_8]: (r1_setfam_1(A_8, k2_setfam_1(A_8, A_8)))), inference(resolution, [status(thm)], [c_16, c_397])).
% 2.49/1.37  tff(c_42, plain, (~r1_setfam_1('#skF_10', k2_setfam_1('#skF_10', '#skF_10'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.49/1.37  tff(c_415, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_412, c_42])).
% 2.49/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.49/1.37  
% 2.49/1.37  Inference rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Ref     : 0
% 2.49/1.37  #Sup     : 90
% 2.49/1.37  #Fact    : 0
% 2.49/1.37  #Define  : 0
% 2.49/1.37  #Split   : 0
% 2.49/1.37  #Chain   : 0
% 2.49/1.37  #Close   : 0
% 2.49/1.37  
% 2.49/1.37  Ordering : KBO
% 2.49/1.37  
% 2.49/1.37  Simplification rules
% 2.49/1.37  ----------------------
% 2.49/1.37  #Subsume      : 8
% 2.49/1.37  #Demod        : 2
% 2.49/1.37  #Tautology    : 11
% 2.49/1.37  #SimpNegUnit  : 0
% 2.49/1.37  #BackRed      : 1
% 2.49/1.37  
% 2.49/1.37  #Partial instantiations: 0
% 2.49/1.37  #Strategies tried      : 1
% 2.49/1.37  
% 2.49/1.37  Timing (in seconds)
% 2.49/1.37  ----------------------
% 2.49/1.38  Preprocessing        : 0.29
% 2.49/1.38  Parsing              : 0.15
% 2.49/1.38  CNF conversion       : 0.03
% 2.49/1.38  Main loop            : 0.31
% 2.49/1.38  Inferencing          : 0.14
% 2.49/1.38  Reduction            : 0.06
% 2.49/1.38  Demodulation         : 0.04
% 2.49/1.38  BG Simplification    : 0.02
% 2.49/1.38  Subsumption          : 0.07
% 2.49/1.38  Abstraction          : 0.01
% 2.49/1.38  MUC search           : 0.00
% 2.49/1.38  Cooper               : 0.00
% 2.49/1.38  Total                : 0.63
% 2.49/1.38  Index Insertion      : 0.00
% 2.49/1.38  Index Deletion       : 0.00
% 2.49/1.38  Index Matching       : 0.00
% 2.49/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
