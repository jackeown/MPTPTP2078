%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   16 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  84 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_62,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_22,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_76,plain,(
    ! [C_28,B_29,A_30] :
      ( r2_hidden(C_28,B_29)
      | ~ r2_hidden(C_28,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_6,B_7,B_29] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_29)
      | ~ r1_tarski(B_7,B_29)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_76])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_175,plain,(
    ! [A_42,B_43,B_44] :
      ( r2_hidden('#skF_2'(A_42,B_43),B_44)
      | ~ r1_tarski(A_42,B_44)
      | r1_xboole_0(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_12,c_76])).

tff(c_20,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_41,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_5')
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_20,c_41])).

tff(c_218,plain,(
    ! [A_48,B_49] :
      ( ~ r2_hidden('#skF_2'(A_48,B_49),'#skF_4')
      | ~ r1_tarski(A_48,'#skF_5')
      | r1_xboole_0(A_48,B_49) ) ),
    inference(resolution,[status(thm)],[c_175,c_47])).

tff(c_304,plain,(
    ! [A_59,B_60] :
      ( ~ r1_tarski(A_59,'#skF_5')
      | ~ r1_tarski(B_60,'#skF_4')
      | r1_xboole_0(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_84,c_218])).

tff(c_16,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_313,plain,(
    ! [B_61] :
      ( k1_xboole_0 = B_61
      | ~ r1_tarski(B_61,'#skF_5')
      | ~ r1_tarski(B_61,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_304,c_16])).

tff(c_324,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_313])).

tff(c_332,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_324])).

tff(c_334,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_332])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:24:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  
% 2.06/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.06/1.28  
% 2.06/1.28  %Foreground sorts:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Background operators:
% 2.06/1.28  
% 2.06/1.28  
% 2.06/1.28  %Foreground operators:
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.28  
% 2.06/1.29  tff(f_71, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.06/1.29  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.29  tff(f_62, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 2.06/1.29  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.29  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.29  tff(c_22, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.29  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.29  tff(c_76, plain, (![C_28, B_29, A_30]: (r2_hidden(C_28, B_29) | ~r2_hidden(C_28, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.29  tff(c_84, plain, (![A_6, B_7, B_29]: (r2_hidden('#skF_2'(A_6, B_7), B_29) | ~r1_tarski(B_7, B_29) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_10, c_76])).
% 2.06/1.29  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.29  tff(c_175, plain, (![A_42, B_43, B_44]: (r2_hidden('#skF_2'(A_42, B_43), B_44) | ~r1_tarski(A_42, B_44) | r1_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_12, c_76])).
% 2.06/1.29  tff(c_20, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.29  tff(c_41, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.29  tff(c_47, plain, (![C_24]: (~r2_hidden(C_24, '#skF_5') | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_20, c_41])).
% 2.06/1.29  tff(c_218, plain, (![A_48, B_49]: (~r2_hidden('#skF_2'(A_48, B_49), '#skF_4') | ~r1_tarski(A_48, '#skF_5') | r1_xboole_0(A_48, B_49))), inference(resolution, [status(thm)], [c_175, c_47])).
% 2.06/1.29  tff(c_304, plain, (![A_59, B_60]: (~r1_tarski(A_59, '#skF_5') | ~r1_tarski(B_60, '#skF_4') | r1_xboole_0(A_59, B_60))), inference(resolution, [status(thm)], [c_84, c_218])).
% 2.06/1.29  tff(c_16, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.29  tff(c_313, plain, (![B_61]: (k1_xboole_0=B_61 | ~r1_tarski(B_61, '#skF_5') | ~r1_tarski(B_61, '#skF_4'))), inference(resolution, [status(thm)], [c_304, c_16])).
% 2.06/1.29  tff(c_324, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_313])).
% 2.06/1.29  tff(c_332, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_324])).
% 2.06/1.29  tff(c_334, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_332])).
% 2.06/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  Inference rules
% 2.06/1.29  ----------------------
% 2.06/1.29  #Ref     : 0
% 2.06/1.29  #Sup     : 60
% 2.06/1.29  #Fact    : 0
% 2.06/1.29  #Define  : 0
% 2.06/1.29  #Split   : 2
% 2.06/1.29  #Chain   : 0
% 2.06/1.30  #Close   : 0
% 2.06/1.30  
% 2.06/1.30  Ordering : KBO
% 2.06/1.30  
% 2.06/1.30  Simplification rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Subsume      : 11
% 2.06/1.30  #Demod        : 6
% 2.06/1.30  #Tautology    : 11
% 2.06/1.30  #SimpNegUnit  : 1
% 2.06/1.30  #BackRed      : 0
% 2.06/1.30  
% 2.06/1.30  #Partial instantiations: 0
% 2.06/1.30  #Strategies tried      : 1
% 2.06/1.30  
% 2.06/1.30  Timing (in seconds)
% 2.06/1.30  ----------------------
% 2.06/1.30  Preprocessing        : 0.29
% 2.06/1.30  Parsing              : 0.16
% 2.06/1.30  CNF conversion       : 0.02
% 2.06/1.30  Main loop            : 0.23
% 2.06/1.30  Inferencing          : 0.09
% 2.06/1.30  Reduction            : 0.06
% 2.06/1.30  Demodulation         : 0.04
% 2.06/1.30  BG Simplification    : 0.01
% 2.06/1.30  Subsumption          : 0.05
% 2.06/1.30  Abstraction          : 0.01
% 2.06/1.30  MUC search           : 0.00
% 2.06/1.30  Cooper               : 0.00
% 2.06/1.30  Total                : 0.54
% 2.06/1.30  Index Insertion      : 0.00
% 2.06/1.30  Index Deletion       : 0.00
% 2.06/1.30  Index Matching       : 0.00
% 2.06/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
