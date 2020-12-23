%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  84 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 ( 109 expanded)
%              Number of equality atoms :   18 (  70 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
     => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l29_zfmisc_1)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_47,axiom,(
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

tff(c_48,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_46,plain,(
    ! [A_54,B_55] :
      ( r1_xboole_0(k1_tarski(A_54),k1_tarski(B_55))
      | B_55 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_164,plain,(
    ! [A_74,B_75] :
      ( k3_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_xboole_0(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_234,plain,(
    ! [A_87,B_88] :
      ( k3_xboole_0(k1_tarski(A_87),k1_tarski(B_88)) = k1_xboole_0
      | B_88 = A_87 ) ),
    inference(resolution,[status(thm)],[c_46,c_164])).

tff(c_50,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_247,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_50])).

tff(c_260,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_247])).

tff(c_18,plain,(
    ! [A_13] : k3_xboole_0(A_13,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [B_53,A_52] :
      ( r2_hidden(B_53,A_52)
      | k3_xboole_0(A_52,k1_tarski(B_53)) != k1_tarski(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_277,plain,(
    ! [A_52] :
      ( r2_hidden('#skF_2',A_52)
      | k3_xboole_0(A_52,k1_xboole_0) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_44])).

tff(c_288,plain,(
    ! [A_52] : r2_hidden('#skF_2',A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_18,c_277])).

tff(c_22,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_350,plain,(
    ! [A_95,B_96,C_97] :
      ( ~ r1_xboole_0(A_95,B_96)
      | ~ r2_hidden(C_97,B_96)
      | ~ r2_hidden(C_97,A_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_363,plain,(
    ! [C_98,A_99] :
      ( ~ r2_hidden(C_98,k1_xboole_0)
      | ~ r2_hidden(C_98,A_99) ) ),
    inference(resolution,[status(thm)],[c_22,c_350])).

tff(c_366,plain,(
    ! [A_99] : ~ r2_hidden('#skF_2',A_99) ),
    inference(resolution,[status(thm)],[c_288,c_363])).

tff(c_376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:43:50 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  
% 2.13/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.25  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.13/1.25  
% 2.13/1.25  %Foreground sorts:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Background operators:
% 2.13/1.25  
% 2.13/1.25  
% 2.13/1.25  %Foreground operators:
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.13/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.25  
% 2.23/1.26  tff(f_95, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.23/1.26  tff(f_90, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 2.23/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.23/1.26  tff(f_57, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.23/1.26  tff(f_85, axiom, (![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l29_zfmisc_1)).
% 2.23/1.26  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.23/1.26  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.23/1.26  tff(c_48, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.23/1.26  tff(c_46, plain, (![A_54, B_55]: (r1_xboole_0(k1_tarski(A_54), k1_tarski(B_55)) | B_55=A_54)), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.23/1.26  tff(c_164, plain, (![A_74, B_75]: (k3_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.23/1.26  tff(c_234, plain, (![A_87, B_88]: (k3_xboole_0(k1_tarski(A_87), k1_tarski(B_88))=k1_xboole_0 | B_88=A_87)), inference(resolution, [status(thm)], [c_46, c_164])).
% 2.23/1.26  tff(c_50, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.23/1.26  tff(c_247, plain, (k1_tarski('#skF_2')=k1_xboole_0 | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_234, c_50])).
% 2.23/1.26  tff(c_260, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_48, c_247])).
% 2.23/1.26  tff(c_18, plain, (![A_13]: (k3_xboole_0(A_13, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.23/1.26  tff(c_44, plain, (![B_53, A_52]: (r2_hidden(B_53, A_52) | k3_xboole_0(A_52, k1_tarski(B_53))!=k1_tarski(B_53))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.23/1.26  tff(c_277, plain, (![A_52]: (r2_hidden('#skF_2', A_52) | k3_xboole_0(A_52, k1_xboole_0)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_260, c_44])).
% 2.23/1.26  tff(c_288, plain, (![A_52]: (r2_hidden('#skF_2', A_52))), inference(demodulation, [status(thm), theory('equality')], [c_260, c_18, c_277])).
% 2.23/1.26  tff(c_22, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.23/1.26  tff(c_350, plain, (![A_95, B_96, C_97]: (~r1_xboole_0(A_95, B_96) | ~r2_hidden(C_97, B_96) | ~r2_hidden(C_97, A_95))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.23/1.26  tff(c_363, plain, (![C_98, A_99]: (~r2_hidden(C_98, k1_xboole_0) | ~r2_hidden(C_98, A_99))), inference(resolution, [status(thm)], [c_22, c_350])).
% 2.23/1.26  tff(c_366, plain, (![A_99]: (~r2_hidden('#skF_2', A_99))), inference(resolution, [status(thm)], [c_288, c_363])).
% 2.23/1.26  tff(c_376, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_366])).
% 2.23/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.26  
% 2.23/1.26  Inference rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Ref     : 0
% 2.23/1.26  #Sup     : 76
% 2.23/1.26  #Fact    : 0
% 2.23/1.26  #Define  : 0
% 2.23/1.26  #Split   : 1
% 2.23/1.26  #Chain   : 0
% 2.23/1.26  #Close   : 0
% 2.23/1.26  
% 2.23/1.26  Ordering : KBO
% 2.23/1.26  
% 2.23/1.26  Simplification rules
% 2.23/1.26  ----------------------
% 2.23/1.26  #Subsume      : 2
% 2.23/1.26  #Demod        : 26
% 2.23/1.26  #Tautology    : 54
% 2.23/1.26  #SimpNegUnit  : 4
% 2.23/1.26  #BackRed      : 1
% 2.23/1.26  
% 2.23/1.26  #Partial instantiations: 0
% 2.23/1.26  #Strategies tried      : 1
% 2.23/1.26  
% 2.23/1.26  Timing (in seconds)
% 2.23/1.26  ----------------------
% 2.23/1.27  Preprocessing        : 0.31
% 2.23/1.27  Parsing              : 0.17
% 2.23/1.27  CNF conversion       : 0.02
% 2.23/1.27  Main loop            : 0.19
% 2.23/1.27  Inferencing          : 0.08
% 2.23/1.27  Reduction            : 0.06
% 2.23/1.27  Demodulation         : 0.04
% 2.23/1.27  BG Simplification    : 0.01
% 2.23/1.27  Subsumption          : 0.03
% 2.23/1.27  Abstraction          : 0.01
% 2.23/1.27  MUC search           : 0.00
% 2.23/1.27  Cooper               : 0.00
% 2.23/1.27  Total                : 0.53
% 2.23/1.27  Index Insertion      : 0.00
% 2.23/1.27  Index Deletion       : 0.00
% 2.23/1.27  Index Matching       : 0.00
% 2.23/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
