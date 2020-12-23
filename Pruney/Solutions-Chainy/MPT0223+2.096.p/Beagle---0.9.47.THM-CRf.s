%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:29 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  51 expanded)
%              Number of equality atoms :   13 (  18 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_18,plain,(
    ! [B_19] : ~ r1_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k3_xboole_0(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [A_26,B_27] : k3_xboole_0(A_26,k2_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_56,plain,(
    ! [A_8] : k3_xboole_0(A_8,A_8) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_165,plain,(
    ! [A_48,B_49] :
      ( r2_hidden('#skF_1'(A_48,B_49),k3_xboole_0(A_48,B_49))
      | r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_181,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_1'(A_50,A_50),A_50)
      | r1_xboole_0(A_50,A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_165])).

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_20,B_21] :
      ( r1_xboole_0(k1_tarski(A_20),k1_tarski(B_21))
      | B_21 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_24,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_124,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_130,plain,(
    ! [C_38] :
      ( ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3'))
      | ~ r2_hidden(C_38,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_124])).

tff(c_154,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_130])).

tff(c_157,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_20,c_154])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_157])).

tff(c_162,plain,(
    ! [C_38] : ~ r2_hidden(C_38,k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_130])).

tff(c_185,plain,(
    r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_181,c_162])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_185])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:14:17 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  
% 1.67/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.16  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.67/1.16  
% 1.67/1.16  %Foreground sorts:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Background operators:
% 1.67/1.16  
% 1.67/1.16  
% 1.67/1.16  %Foreground operators:
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.67/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.67/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.67/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.67/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.67/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.67/1.16  
% 1.67/1.17  tff(f_56, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.67/1.17  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.67/1.17  tff(f_41, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.67/1.17  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.67/1.17  tff(f_66, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.67/1.17  tff(f_61, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.67/1.17  tff(c_18, plain, (![B_19]: (~r1_xboole_0(k1_tarski(B_19), k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.67/1.17  tff(c_8, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k3_xboole_0(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.67/1.17  tff(c_44, plain, (![A_26, B_27]: (k3_xboole_0(A_26, k2_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.17  tff(c_56, plain, (![A_8]: (k3_xboole_0(A_8, A_8)=A_8)), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 1.67/1.17  tff(c_165, plain, (![A_48, B_49]: (r2_hidden('#skF_1'(A_48, B_49), k3_xboole_0(A_48, B_49)) | r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.17  tff(c_181, plain, (![A_50]: (r2_hidden('#skF_1'(A_50, A_50), A_50) | r1_xboole_0(A_50, A_50))), inference(superposition, [status(thm), theory('equality')], [c_56, c_165])).
% 1.67/1.17  tff(c_22, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.67/1.17  tff(c_20, plain, (![A_20, B_21]: (r1_xboole_0(k1_tarski(A_20), k1_tarski(B_21)) | B_21=A_20)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.67/1.17  tff(c_24, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.67/1.17  tff(c_124, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.67/1.17  tff(c_130, plain, (![C_38]: (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3')) | ~r2_hidden(C_38, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_24, c_124])).
% 1.67/1.17  tff(c_154, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_130])).
% 1.67/1.17  tff(c_157, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_20, c_154])).
% 1.67/1.17  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_157])).
% 1.67/1.17  tff(c_162, plain, (![C_38]: (~r2_hidden(C_38, k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_130])).
% 1.67/1.17  tff(c_185, plain, (r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_181, c_162])).
% 1.67/1.17  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_185])).
% 1.67/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.17  
% 1.67/1.17  Inference rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Ref     : 0
% 1.67/1.17  #Sup     : 39
% 1.67/1.17  #Fact    : 0
% 1.67/1.17  #Define  : 0
% 1.67/1.17  #Split   : 1
% 1.67/1.17  #Chain   : 0
% 1.67/1.17  #Close   : 0
% 1.67/1.17  
% 1.67/1.17  Ordering : KBO
% 1.67/1.17  
% 1.67/1.17  Simplification rules
% 1.67/1.17  ----------------------
% 1.67/1.17  #Subsume      : 2
% 1.67/1.17  #Demod        : 4
% 1.67/1.17  #Tautology    : 25
% 1.67/1.17  #SimpNegUnit  : 3
% 1.67/1.17  #BackRed      : 0
% 1.67/1.17  
% 1.67/1.17  #Partial instantiations: 0
% 1.67/1.17  #Strategies tried      : 1
% 1.67/1.17  
% 1.67/1.17  Timing (in seconds)
% 1.67/1.17  ----------------------
% 1.67/1.18  Preprocessing        : 0.29
% 1.67/1.18  Parsing              : 0.15
% 1.67/1.18  CNF conversion       : 0.02
% 1.67/1.18  Main loop            : 0.13
% 1.67/1.18  Inferencing          : 0.05
% 1.67/1.18  Reduction            : 0.04
% 1.67/1.18  Demodulation         : 0.03
% 1.67/1.18  BG Simplification    : 0.01
% 1.67/1.18  Subsumption          : 0.02
% 1.67/1.18  Abstraction          : 0.01
% 1.67/1.18  MUC search           : 0.00
% 1.67/1.18  Cooper               : 0.00
% 1.67/1.18  Total                : 0.44
% 1.67/1.18  Index Insertion      : 0.00
% 1.67/1.18  Index Deletion       : 0.00
% 1.67/1.18  Index Matching       : 0.00
% 1.67/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
