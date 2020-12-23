%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:31 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   38 (  57 expanded)
%              Number of leaves         :   15 (  27 expanded)
%              Depth                    :    8
%              Number of atoms          :   67 ( 135 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_ordinal1,type,(
    r1_ordinal1: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v3_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ~ ( ~ r2_xboole_0(A,B)
                & A != B
                & ~ r2_xboole_0(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_ordinal1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v3_ordinal1(A)
        & v3_ordinal1(B) )
     => ( r1_ordinal1(A,B)
      <=> r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r1_ordinal1(A,B)
            | r2_hidden(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_ordinal1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',antisymmetry_r2_hidden)).

tff(c_24,plain,(
    v3_ordinal1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    v3_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( r1_tarski(A_20,B_21)
      | ~ r1_ordinal1(A_20,B_21)
      | ~ v3_ordinal1(B_21)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_16,B_17] :
      ( r2_xboole_0(A_16,B_17)
      | B_17 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ~ r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_20])).

tff(c_45,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_34])).

tff(c_61,plain,
    ( ~ r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_55,c_45])).

tff(c_67,plain,(
    ~ r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_61])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( r2_hidden(B_9,A_7)
      | r1_ordinal1(A_7,B_9)
      | ~ v3_ordinal1(B_9)
      | ~ v3_ordinal1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_51,plain,(
    ! [B_18,A_19] :
      ( r2_hidden(B_18,A_19)
      | r1_ordinal1(A_19,B_18)
      | ~ v3_ordinal1(B_18)
      | ~ v3_ordinal1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( ~ r2_hidden(B_2,A_1)
      | ~ r2_hidden(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_73,plain,(
    ! [A_24,B_25] :
      ( ~ r2_hidden(A_24,B_25)
      | r1_ordinal1(A_24,B_25)
      | ~ v3_ordinal1(B_25)
      | ~ v3_ordinal1(A_24) ) ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_92,plain,(
    ! [B_26,A_27] :
      ( r1_ordinal1(B_26,A_27)
      | r1_ordinal1(A_27,B_26)
      | ~ v3_ordinal1(B_26)
      | ~ v3_ordinal1(A_27) ) ),
    inference(resolution,[status(thm)],[c_14,c_73])).

tff(c_16,plain,(
    ~ r2_xboole_0('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_41,plain,
    ( '#skF_2' = '#skF_1'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_16])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_41])).

tff(c_58,plain,
    ( ~ r1_ordinal1('#skF_2','#skF_1')
    | ~ v3_ordinal1('#skF_1')
    | ~ v3_ordinal1('#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_50])).

tff(c_64,plain,(
    ~ r1_ordinal1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24,c_58])).

tff(c_96,plain,
    ( r1_ordinal1('#skF_1','#skF_2')
    | ~ v3_ordinal1('#skF_2')
    | ~ v3_ordinal1('#skF_1') ),
    inference(resolution,[status(thm)],[c_92,c_64])).

tff(c_103,plain,(
    r1_ordinal1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_22,c_96])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_103])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:10:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  
% 1.61/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.14  %$ r2_xboole_0 > r2_hidden > r1_tarski > r1_ordinal1 > v3_ordinal1 > #nlpp > #skF_2 > #skF_1
% 1.61/1.14  
% 1.61/1.14  %Foreground sorts:
% 1.61/1.14  
% 1.61/1.14  
% 1.61/1.14  %Background operators:
% 1.61/1.14  
% 1.61/1.14  
% 1.61/1.14  %Foreground operators:
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.14  tff(r1_ordinal1, type, r1_ordinal1: ($i * $i) > $o).
% 1.61/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.14  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.61/1.14  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.14  
% 1.77/1.15  tff(f_70, negated_conjecture, ~(![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => ~((~r2_xboole_0(A, B) & ~(A = B)) & ~r2_xboole_0(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_ordinal1)).
% 1.77/1.15  tff(f_45, axiom, (![A, B]: ((v3_ordinal1(A) & v3_ordinal1(B)) => (r1_ordinal1(A, B) <=> r1_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r1_ordinal1)).
% 1.77/1.15  tff(f_37, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 1.77/1.15  tff(f_54, axiom, (![A]: (v3_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r1_ordinal1(A, B) | r2_hidden(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_ordinal1)).
% 1.77/1.15  tff(f_30, axiom, (![A, B]: (r2_hidden(A, B) => ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', antisymmetry_r2_hidden)).
% 1.77/1.15  tff(c_24, plain, (v3_ordinal1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.15  tff(c_22, plain, (v3_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.15  tff(c_55, plain, (![A_20, B_21]: (r1_tarski(A_20, B_21) | ~r1_ordinal1(A_20, B_21) | ~v3_ordinal1(B_21) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.77/1.15  tff(c_18, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.15  tff(c_28, plain, (![A_16, B_17]: (r2_xboole_0(A_16, B_17) | B_17=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.77/1.15  tff(c_20, plain, (~r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.15  tff(c_34, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_20])).
% 1.77/1.15  tff(c_45, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_18, c_34])).
% 1.77/1.15  tff(c_61, plain, (~r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_55, c_45])).
% 1.77/1.15  tff(c_67, plain, (~r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_61])).
% 1.77/1.15  tff(c_14, plain, (![B_9, A_7]: (r2_hidden(B_9, A_7) | r1_ordinal1(A_7, B_9) | ~v3_ordinal1(B_9) | ~v3_ordinal1(A_7))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.15  tff(c_51, plain, (![B_18, A_19]: (r2_hidden(B_18, A_19) | r1_ordinal1(A_19, B_18) | ~v3_ordinal1(B_18) | ~v3_ordinal1(A_19))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.77/1.15  tff(c_2, plain, (![B_2, A_1]: (~r2_hidden(B_2, A_1) | ~r2_hidden(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.77/1.15  tff(c_73, plain, (![A_24, B_25]: (~r2_hidden(A_24, B_25) | r1_ordinal1(A_24, B_25) | ~v3_ordinal1(B_25) | ~v3_ordinal1(A_24))), inference(resolution, [status(thm)], [c_51, c_2])).
% 1.77/1.15  tff(c_92, plain, (![B_26, A_27]: (r1_ordinal1(B_26, A_27) | r1_ordinal1(A_27, B_26) | ~v3_ordinal1(B_26) | ~v3_ordinal1(A_27))), inference(resolution, [status(thm)], [c_14, c_73])).
% 1.77/1.15  tff(c_16, plain, (~r2_xboole_0('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.77/1.15  tff(c_41, plain, ('#skF_2'='#skF_1' | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_28, c_16])).
% 1.77/1.15  tff(c_50, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_18, c_41])).
% 1.77/1.15  tff(c_58, plain, (~r1_ordinal1('#skF_2', '#skF_1') | ~v3_ordinal1('#skF_1') | ~v3_ordinal1('#skF_2')), inference(resolution, [status(thm)], [c_55, c_50])).
% 1.77/1.15  tff(c_64, plain, (~r1_ordinal1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24, c_58])).
% 1.77/1.15  tff(c_96, plain, (r1_ordinal1('#skF_1', '#skF_2') | ~v3_ordinal1('#skF_2') | ~v3_ordinal1('#skF_1')), inference(resolution, [status(thm)], [c_92, c_64])).
% 1.77/1.15  tff(c_103, plain, (r1_ordinal1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_24, c_22, c_96])).
% 1.77/1.15  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_103])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 11
% 1.77/1.15  #Fact    : 2
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 0
% 1.77/1.16  #Chain   : 0
% 1.77/1.16  #Close   : 0
% 1.77/1.16  
% 1.77/1.16  Ordering : KBO
% 1.77/1.16  
% 1.77/1.16  Simplification rules
% 1.77/1.16  ----------------------
% 1.77/1.16  #Subsume      : 0
% 1.77/1.16  #Demod        : 6
% 1.77/1.16  #Tautology    : 3
% 1.77/1.16  #SimpNegUnit  : 3
% 1.77/1.16  #BackRed      : 0
% 1.77/1.16  
% 1.77/1.16  #Partial instantiations: 0
% 1.77/1.16  #Strategies tried      : 1
% 1.77/1.16  
% 1.77/1.16  Timing (in seconds)
% 1.77/1.16  ----------------------
% 1.77/1.16  Preprocessing        : 0.25
% 1.77/1.16  Parsing              : 0.13
% 1.77/1.16  CNF conversion       : 0.02
% 1.77/1.16  Main loop            : 0.11
% 1.77/1.16  Inferencing          : 0.04
% 1.77/1.16  Reduction            : 0.03
% 1.77/1.16  Demodulation         : 0.01
% 1.77/1.16  BG Simplification    : 0.01
% 1.77/1.16  Subsumption          : 0.02
% 1.77/1.16  Abstraction          : 0.00
% 1.77/1.16  MUC search           : 0.00
% 1.77/1.16  Cooper               : 0.00
% 1.77/1.16  Total                : 0.38
% 1.77/1.16  Index Insertion      : 0.00
% 1.77/1.16  Index Deletion       : 0.00
% 1.77/1.16  Index Matching       : 0.00
% 1.77/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
