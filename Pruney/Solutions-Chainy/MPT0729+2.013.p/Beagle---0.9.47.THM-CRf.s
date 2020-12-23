%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:59 EST 2020

% Result     : Theorem 5.81s
% Output     : CNFRefutation 5.81s
% Verified   : 
% Statistics : Number of formulae       :   36 (  50 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  71 expanded)
%              Number of equality atoms :   14 (  29 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( k1_ordinal1(A) = k1_ordinal1(B)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_ordinal1)).

tff(f_50,axiom,(
    ! [A] : r2_hidden(A,k1_ordinal1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_ordinal1)).

tff(f_48,axiom,(
    ! [A] : k1_ordinal1(A) = k2_xboole_0(A,k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_ordinal1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_38,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    k1_ordinal1('#skF_5') = k1_ordinal1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    ! [A_17] : r2_hidden(A_17,k1_ordinal1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_49,plain,(
    r2_hidden('#skF_5',k1_ordinal1('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_46])).

tff(c_34,plain,(
    ! [A_14] : k2_xboole_0(A_14,k1_tarski(A_14)) = k1_ordinal1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_170,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | r2_hidden(D_38,A_40)
      | ~ r2_hidden(D_38,k2_xboole_0(A_40,B_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_3544,plain,(
    ! [D_2096,A_2097] :
      ( r2_hidden(D_2096,k1_tarski(A_2097))
      | r2_hidden(D_2096,A_2097)
      | ~ r2_hidden(D_2096,k1_ordinal1(A_2097)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_170])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4430,plain,(
    ! [D_2331,A_2332] :
      ( D_2331 = A_2332
      | r2_hidden(D_2331,A_2332)
      | ~ r2_hidden(D_2331,k1_ordinal1(A_2332)) ) ),
    inference(resolution,[status(thm)],[c_3544,c_22])).

tff(c_4472,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_49,c_4430])).

tff(c_4491,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4472])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_4496,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_4491,c_2])).

tff(c_36,plain,(
    ! [A_15] : r2_hidden(A_15,k1_ordinal1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4759,plain,(
    ! [D_2435] :
      ( D_2435 = '#skF_5'
      | r2_hidden(D_2435,'#skF_5')
      | ~ r2_hidden(D_2435,k1_ordinal1('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_4430])).

tff(c_4805,plain,
    ( '#skF_5' = '#skF_6'
    | r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_36,c_4759])).

tff(c_4821,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4496,c_38,c_4805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:12:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.81/2.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.13  
% 5.81/2.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.14  %$ r2_hidden > k2_xboole_0 > #nlpp > k1_tarski > k1_ordinal1 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 5.81/2.14  
% 5.81/2.14  %Foreground sorts:
% 5.81/2.14  
% 5.81/2.14  
% 5.81/2.14  %Background operators:
% 5.81/2.14  
% 5.81/2.14  
% 5.81/2.14  %Foreground operators:
% 5.81/2.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.81/2.14  tff(k1_ordinal1, type, k1_ordinal1: $i > $i).
% 5.81/2.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.81/2.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.81/2.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.81/2.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 5.81/2.14  tff('#skF_5', type, '#skF_5': $i).
% 5.81/2.14  tff('#skF_6', type, '#skF_6': $i).
% 5.81/2.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 5.81/2.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.81/2.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.81/2.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.81/2.14  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 5.81/2.14  
% 5.81/2.14  tff(f_55, negated_conjecture, ~(![A, B]: ((k1_ordinal1(A) = k1_ordinal1(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_ordinal1)).
% 5.81/2.14  tff(f_50, axiom, (![A]: r2_hidden(A, k1_ordinal1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_ordinal1)).
% 5.81/2.14  tff(f_48, axiom, (![A]: (k1_ordinal1(A) = k2_xboole_0(A, k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_ordinal1)).
% 5.81/2.14  tff(f_39, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 5.81/2.14  tff(f_46, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 5.81/2.14  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 5.81/2.14  tff(c_38, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.14  tff(c_40, plain, (k1_ordinal1('#skF_5')=k1_ordinal1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.81/2.14  tff(c_46, plain, (![A_17]: (r2_hidden(A_17, k1_ordinal1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.81/2.14  tff(c_49, plain, (r2_hidden('#skF_5', k1_ordinal1('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_40, c_46])).
% 5.81/2.14  tff(c_34, plain, (![A_14]: (k2_xboole_0(A_14, k1_tarski(A_14))=k1_ordinal1(A_14))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.81/2.14  tff(c_170, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | r2_hidden(D_38, A_40) | ~r2_hidden(D_38, k2_xboole_0(A_40, B_39)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.81/2.14  tff(c_3544, plain, (![D_2096, A_2097]: (r2_hidden(D_2096, k1_tarski(A_2097)) | r2_hidden(D_2096, A_2097) | ~r2_hidden(D_2096, k1_ordinal1(A_2097)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_170])).
% 5.81/2.14  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 5.81/2.14  tff(c_4430, plain, (![D_2331, A_2332]: (D_2331=A_2332 | r2_hidden(D_2331, A_2332) | ~r2_hidden(D_2331, k1_ordinal1(A_2332)))), inference(resolution, [status(thm)], [c_3544, c_22])).
% 5.81/2.14  tff(c_4472, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_49, c_4430])).
% 5.81/2.14  tff(c_4491, plain, (r2_hidden('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_4472])).
% 5.81/2.14  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 5.81/2.14  tff(c_4496, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_4491, c_2])).
% 5.81/2.14  tff(c_36, plain, (![A_15]: (r2_hidden(A_15, k1_ordinal1(A_15)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.81/2.14  tff(c_4759, plain, (![D_2435]: (D_2435='#skF_5' | r2_hidden(D_2435, '#skF_5') | ~r2_hidden(D_2435, k1_ordinal1('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_40, c_4430])).
% 5.81/2.14  tff(c_4805, plain, ('#skF_5'='#skF_6' | r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_36, c_4759])).
% 5.81/2.14  tff(c_4821, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4496, c_38, c_4805])).
% 5.81/2.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.81/2.14  
% 5.81/2.14  Inference rules
% 5.81/2.14  ----------------------
% 5.81/2.14  #Ref     : 0
% 5.81/2.14  #Sup     : 935
% 5.81/2.14  #Fact    : 6
% 5.81/2.14  #Define  : 0
% 5.81/2.14  #Split   : 1
% 5.81/2.14  #Chain   : 0
% 5.81/2.14  #Close   : 0
% 5.81/2.14  
% 5.81/2.14  Ordering : KBO
% 5.81/2.14  
% 5.81/2.14  Simplification rules
% 5.81/2.14  ----------------------
% 5.81/2.14  #Subsume      : 160
% 5.81/2.14  #Demod        : 143
% 5.81/2.14  #Tautology    : 21
% 5.81/2.14  #SimpNegUnit  : 24
% 5.81/2.14  #BackRed      : 0
% 5.81/2.14  
% 5.81/2.14  #Partial instantiations: 1404
% 5.81/2.14  #Strategies tried      : 1
% 5.81/2.14  
% 5.81/2.14  Timing (in seconds)
% 5.81/2.14  ----------------------
% 5.81/2.15  Preprocessing        : 0.32
% 5.81/2.15  Parsing              : 0.16
% 5.81/2.15  CNF conversion       : 0.03
% 5.81/2.15  Main loop            : 1.13
% 5.81/2.15  Inferencing          : 0.41
% 5.81/2.15  Reduction            : 0.30
% 5.81/2.15  Demodulation         : 0.19
% 5.81/2.15  BG Simplification    : 0.05
% 5.81/2.15  Subsumption          : 0.29
% 5.81/2.15  Abstraction          : 0.05
% 5.81/2.15  MUC search           : 0.00
% 5.81/2.15  Cooper               : 0.00
% 5.81/2.15  Total                : 1.47
% 5.81/2.15  Index Insertion      : 0.00
% 5.81/2.15  Index Deletion       : 0.00
% 5.81/2.15  Index Matching       : 0.00
% 5.81/2.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
