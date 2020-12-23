%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:47 EST 2020

% Result     : Theorem 9.05s
% Output     : CNFRefutation 9.05s
% Verified   : 
% Statistics : Number of formulae       :   31 (  42 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   48 (  86 expanded)
%              Number of equality atoms :   15 (  26 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,(
    ~ r2_hidden('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_28,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_xboole_0(k2_tarski(A_7,B_8),C_9) = k2_tarski(A_7,B_8)
      | r2_hidden(B_8,C_9)
      | r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r2_hidden('#skF_1'(A_46,B_47,C_48),C_48)
      | r2_hidden('#skF_2'(A_46,B_47,C_48),C_48)
      | k4_xboole_0(A_46,B_47) = C_48 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_164,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_155])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_375,plain,(
    ! [A_71,B_72,C_73] :
      ( ~ r2_hidden('#skF_1'(A_71,B_72,C_73),C_73)
      | r2_hidden('#skF_2'(A_71,B_72,C_73),B_72)
      | ~ r2_hidden('#skF_2'(A_71,B_72,C_73),A_71)
      | k4_xboole_0(A_71,B_72) = C_73 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_971,plain,(
    ! [A_92,B_93] :
      ( r2_hidden('#skF_2'(A_92,B_93,A_92),B_93)
      | ~ r2_hidden('#skF_2'(A_92,B_93,A_92),A_92)
      | k4_xboole_0(A_92,B_93) = A_92 ) ),
    inference(resolution,[status(thm)],[c_12,c_375])).

tff(c_985,plain,(
    ! [A_94,B_95] :
      ( r2_hidden('#skF_2'(A_94,B_95,A_94),B_95)
      | k4_xboole_0(A_94,B_95) = A_94 ) ),
    inference(resolution,[status(thm)],[c_164,c_971])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10182,plain,(
    ! [A_255,A_256,B_257] :
      ( ~ r2_hidden('#skF_2'(A_255,k4_xboole_0(A_256,B_257),A_255),B_257)
      | k4_xboole_0(A_255,k4_xboole_0(A_256,B_257)) = A_255 ) ),
    inference(resolution,[status(thm)],[c_985,c_4])).

tff(c_10327,plain,(
    ! [A_258,A_259] : k4_xboole_0(A_258,k4_xboole_0(A_259,A_258)) = A_258 ),
    inference(resolution,[status(thm)],[c_164,c_10182])).

tff(c_11914,plain,(
    ! [C_280,A_281,B_282] :
      ( k4_xboole_0(C_280,k2_tarski(A_281,B_282)) = C_280
      | r2_hidden(B_282,C_280)
      | r2_hidden(A_281,C_280) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_10327])).

tff(c_26,plain,(
    k4_xboole_0('#skF_5',k2_tarski('#skF_3','#skF_4')) != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12277,plain,
    ( r2_hidden('#skF_4','#skF_5')
    | r2_hidden('#skF_3','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_11914,c_26])).

tff(c_12410,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_12277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:12:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.05/3.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.17  
% 9.05/3.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.17  %$ r2_hidden > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 9.05/3.17  
% 9.05/3.17  %Foreground sorts:
% 9.05/3.17  
% 9.05/3.17  
% 9.05/3.17  %Background operators:
% 9.05/3.17  
% 9.05/3.17  
% 9.05/3.17  %Foreground operators:
% 9.05/3.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 9.05/3.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.05/3.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.05/3.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.05/3.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.05/3.17  tff('#skF_5', type, '#skF_5': $i).
% 9.05/3.17  tff('#skF_3', type, '#skF_3': $i).
% 9.05/3.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.05/3.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.05/3.17  tff('#skF_4', type, '#skF_4': $i).
% 9.05/3.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.05/3.17  
% 9.05/3.18  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 9.05/3.18  tff(f_43, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 9.05/3.18  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 9.05/3.18  tff(c_30, plain, (~r2_hidden('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.05/3.18  tff(c_28, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.05/3.18  tff(c_20, plain, (![A_7, B_8, C_9]: (k4_xboole_0(k2_tarski(A_7, B_8), C_9)=k2_tarski(A_7, B_8) | r2_hidden(B_8, C_9) | r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.05/3.18  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.18  tff(c_155, plain, (![A_46, B_47, C_48]: (~r2_hidden('#skF_1'(A_46, B_47, C_48), C_48) | r2_hidden('#skF_2'(A_46, B_47, C_48), C_48) | k4_xboole_0(A_46, B_47)=C_48)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.18  tff(c_164, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_155])).
% 9.05/3.18  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.18  tff(c_375, plain, (![A_71, B_72, C_73]: (~r2_hidden('#skF_1'(A_71, B_72, C_73), C_73) | r2_hidden('#skF_2'(A_71, B_72, C_73), B_72) | ~r2_hidden('#skF_2'(A_71, B_72, C_73), A_71) | k4_xboole_0(A_71, B_72)=C_73)), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.18  tff(c_971, plain, (![A_92, B_93]: (r2_hidden('#skF_2'(A_92, B_93, A_92), B_93) | ~r2_hidden('#skF_2'(A_92, B_93, A_92), A_92) | k4_xboole_0(A_92, B_93)=A_92)), inference(resolution, [status(thm)], [c_12, c_375])).
% 9.05/3.18  tff(c_985, plain, (![A_94, B_95]: (r2_hidden('#skF_2'(A_94, B_95, A_94), B_95) | k4_xboole_0(A_94, B_95)=A_94)), inference(resolution, [status(thm)], [c_164, c_971])).
% 9.05/3.18  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.05/3.18  tff(c_10182, plain, (![A_255, A_256, B_257]: (~r2_hidden('#skF_2'(A_255, k4_xboole_0(A_256, B_257), A_255), B_257) | k4_xboole_0(A_255, k4_xboole_0(A_256, B_257))=A_255)), inference(resolution, [status(thm)], [c_985, c_4])).
% 9.05/3.18  tff(c_10327, plain, (![A_258, A_259]: (k4_xboole_0(A_258, k4_xboole_0(A_259, A_258))=A_258)), inference(resolution, [status(thm)], [c_164, c_10182])).
% 9.05/3.18  tff(c_11914, plain, (![C_280, A_281, B_282]: (k4_xboole_0(C_280, k2_tarski(A_281, B_282))=C_280 | r2_hidden(B_282, C_280) | r2_hidden(A_281, C_280))), inference(superposition, [status(thm), theory('equality')], [c_20, c_10327])).
% 9.05/3.18  tff(c_26, plain, (k4_xboole_0('#skF_5', k2_tarski('#skF_3', '#skF_4'))!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.05/3.18  tff(c_12277, plain, (r2_hidden('#skF_4', '#skF_5') | r2_hidden('#skF_3', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_11914, c_26])).
% 9.05/3.18  tff(c_12410, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_12277])).
% 9.05/3.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.05/3.18  
% 9.05/3.18  Inference rules
% 9.05/3.18  ----------------------
% 9.05/3.18  #Ref     : 0
% 9.05/3.18  #Sup     : 3522
% 9.05/3.18  #Fact    : 0
% 9.05/3.18  #Define  : 0
% 9.05/3.18  #Split   : 0
% 9.05/3.18  #Chain   : 0
% 9.05/3.18  #Close   : 0
% 9.05/3.18  
% 9.05/3.18  Ordering : KBO
% 9.05/3.18  
% 9.05/3.18  Simplification rules
% 9.05/3.18  ----------------------
% 9.05/3.18  #Subsume      : 1908
% 9.05/3.18  #Demod        : 1270
% 9.05/3.18  #Tautology    : 431
% 9.05/3.18  #SimpNegUnit  : 230
% 9.05/3.18  #BackRed      : 2
% 9.05/3.18  
% 9.05/3.18  #Partial instantiations: 0
% 9.05/3.18  #Strategies tried      : 1
% 9.05/3.18  
% 9.05/3.18  Timing (in seconds)
% 9.05/3.18  ----------------------
% 9.05/3.19  Preprocessing        : 0.27
% 9.05/3.19  Parsing              : 0.14
% 9.05/3.19  CNF conversion       : 0.02
% 9.05/3.19  Main loop            : 2.16
% 9.05/3.19  Inferencing          : 0.61
% 9.05/3.19  Reduction            : 0.96
% 9.05/3.19  Demodulation         : 0.79
% 9.05/3.19  BG Simplification    : 0.07
% 9.05/3.19  Subsumption          : 0.42
% 9.05/3.19  Abstraction          : 0.11
% 9.05/3.19  MUC search           : 0.00
% 9.05/3.19  Cooper               : 0.00
% 9.05/3.19  Total                : 2.46
% 9.05/3.19  Index Insertion      : 0.00
% 9.05/3.19  Index Deletion       : 0.00
% 9.05/3.19  Index Matching       : 0.00
% 9.05/3.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
