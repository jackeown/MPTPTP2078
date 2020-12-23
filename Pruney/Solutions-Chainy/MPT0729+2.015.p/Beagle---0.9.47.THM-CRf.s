%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 6.31s
% Output     : CNFRefutation 6.31s
% Verified   : 
% Statistics : Number of formulae       :   40 (  57 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  85 expanded)
%              Number of equality atoms :   20 (  41 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_54,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_52,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_48,plain,(
    k1_ordinal1('#skF_5') = k1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    ! [A_18] : r2_hidden(A_18,k1_ordinal1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_56,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_53])).

tff(c_42,plain,(
    ! [A_16] : k2_xboole_0(A_16,k1_tarski(A_16)) = k1_ordinal1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_270,plain,(
    ! [D_54,B_55,A_56] :
      ( r2_hidden(D_54,B_55)
      | r2_hidden(D_54,A_56)
      | ~ r2_hidden(D_54,k2_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2580,plain,(
    ! [D_271,A_272] :
      ( r2_hidden(D_271,k1_tarski(A_272))
      | r2_hidden(D_271,A_272)
      | ~ r2_hidden(D_271,k1_ordinal1(A_272)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_270])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_242,plain,(
    ! [D_50,B_51,A_52] :
      ( D_50 = B_51
      | D_50 = A_52
      | ~ r2_hidden(D_50,k2_tarski(A_52,B_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_251,plain,(
    ! [D_50,A_15] :
      ( D_50 = A_15
      | D_50 = A_15
      | ~ r2_hidden(D_50,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_242])).

tff(c_4355,plain,(
    ! [D_372,A_373] :
      ( D_372 = A_373
      | r2_hidden(D_372,A_373)
      | ~ r2_hidden(D_372,k1_ordinal1(A_373)) ) ),
    inference(resolution,[status(thm)],[c_2580,c_251])).

tff(c_4424,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_56,c_4355])).

tff(c_4450,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_4424])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4455,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_4450,c_2])).

tff(c_44,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_4527,plain,(
    ! [D_377] :
      ( D_377 = '#skF_5'
      | r2_hidden(D_377,'#skF_5')
      | ~ r2_hidden(D_377,k1_ordinal1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4355])).

tff(c_4601,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_44,c_4527])).

tff(c_4624,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4455,c_46,c_4601])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:35:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.31/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.22  
% 6.31/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.22  %$ r2_hidden > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 6.31/2.22  
% 6.31/2.22  %Foreground sorts:
% 6.31/2.22  
% 6.31/2.22  
% 6.31/2.22  %Background operators:
% 6.31/2.22  
% 6.31/2.22  
% 6.31/2.22  %Foreground operators:
% 6.31/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 6.31/2.22  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.31/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.31/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.31/2.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.31/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.31/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.31/2.22  tff('#skF_6', type, '#skF_6': $i).
% 6.31/2.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.31/2.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.31/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.31/2.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.31/2.23  
% 6.31/2.23  tff(f_59, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_ordinal1)).
% 6.31/2.23  tff(f_54, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_ordinal1)).
% 6.31/2.23  tff(f_52, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_ordinal1)).
% 6.31/2.23  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 6.31/2.23  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.31/2.23  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 6.31/2.23  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 6.31/2.23  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.23  tff(c_48, plain, (k1_ordinal1('#skF_5')=k1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.31/2.23  tff(c_53, plain, (![A_18]: (r2_hidden(A_18, k1_ordinal1(A_18)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.31/2.23  tff(c_56, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_53])).
% 6.31/2.23  tff(c_42, plain, (![A_16]: (k2_xboole_0(A_16, k1_tarski(A_16))=k1_ordinal1(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 6.31/2.23  tff(c_270, plain, (![D_54, B_55, A_56]: (r2_hidden(D_54, B_55) | r2_hidden(D_54, A_56) | ~r2_hidden(D_54, k2_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.31/2.23  tff(c_2580, plain, (![D_271, A_272]: (r2_hidden(D_271, k1_tarski(A_272)) | r2_hidden(D_271, A_272) | ~r2_hidden(D_271, k1_ordinal1(A_272)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_270])).
% 6.31/2.23  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.31/2.23  tff(c_242, plain, (![D_50, B_51, A_52]: (D_50=B_51 | D_50=A_52 | ~r2_hidden(D_50, k2_tarski(A_52, B_51)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.31/2.23  tff(c_251, plain, (![D_50, A_15]: (D_50=A_15 | D_50=A_15 | ~r2_hidden(D_50, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_242])).
% 6.31/2.23  tff(c_4355, plain, (![D_372, A_373]: (D_372=A_373 | r2_hidden(D_372, A_373) | ~r2_hidden(D_372, k1_ordinal1(A_373)))), inference(resolution, [status(thm)], [c_2580, c_251])).
% 6.31/2.23  tff(c_4424, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_56, c_4355])).
% 6.31/2.23  tff(c_4450, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_46, c_4424])).
% 6.31/2.23  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 6.31/2.23  tff(c_4455, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_4450, c_2])).
% 6.31/2.23  tff(c_44, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.31/2.23  tff(c_4527, plain, (![D_377]: (D_377='#skF_5' | r2_hidden(D_377, '#skF_5') | ~r2_hidden(D_377, k1_ordinal1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_4355])).
% 6.31/2.23  tff(c_4601, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_44, c_4527])).
% 6.31/2.23  tff(c_4624, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4455, c_46, c_4601])).
% 6.31/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.31/2.23  
% 6.31/2.23  Inference rules
% 6.31/2.23  ----------------------
% 6.31/2.23  #Ref     : 0
% 6.31/2.23  #Sup     : 957
% 6.31/2.23  #Fact    : 6
% 6.31/2.23  #Define  : 0
% 6.31/2.23  #Split   : 0
% 6.31/2.23  #Chain   : 0
% 6.31/2.23  #Close   : 0
% 6.31/2.23  
% 6.31/2.23  Ordering : KBO
% 6.31/2.23  
% 6.31/2.23  Simplification rules
% 6.31/2.23  ----------------------
% 6.31/2.23  #Subsume      : 215
% 6.31/2.23  #Demod        : 17
% 6.31/2.23  #Tautology    : 28
% 6.31/2.23  #SimpNegUnit  : 32
% 6.31/2.23  #BackRed      : 0
% 6.31/2.23  
% 6.31/2.23  #Partial instantiations: 0
% 6.31/2.23  #Strategies tried      : 1
% 6.31/2.23  
% 6.31/2.23  Timing (in seconds)
% 6.31/2.23  ----------------------
% 6.31/2.24  Preprocessing        : 0.30
% 6.31/2.24  Parsing              : 0.16
% 6.31/2.24  CNF conversion       : 0.02
% 6.31/2.24  Main loop            : 1.17
% 6.31/2.24  Inferencing          : 0.36
% 6.31/2.24  Reduction            : 0.31
% 6.31/2.24  Demodulation         : 0.19
% 6.31/2.24  BG Simplification    : 0.04
% 6.31/2.24  Subsumption          : 0.38
% 6.31/2.24  Abstraction          : 0.05
% 6.31/2.24  MUC search           : 0.00
% 6.31/2.24  Cooper               : 0.00
% 6.31/2.24  Total                : 1.50
% 6.31/2.24  Index Insertion      : 0.00
% 6.31/2.24  Index Deletion       : 0.00
% 6.31/2.24  Index Matching       : 0.00
% 6.31/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
