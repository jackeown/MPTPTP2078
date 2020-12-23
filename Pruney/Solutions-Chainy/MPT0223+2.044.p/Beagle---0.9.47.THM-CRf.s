%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 8.53s
% Output     : CNFRefutation 8.53s
% Verified   : 
% Statistics : Number of formulae       :   45 (  48 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  60 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(c_64,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_46,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_135,plain,(
    ! [A_51,B_52] : k1_enumset1(A_51,A_51,B_52) = k2_tarski(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    ! [E_16,B_11,C_12] : r2_hidden(E_16,k1_enumset1(E_16,B_11,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_141,plain,(
    ! [A_51,B_52] : r2_hidden(A_51,k2_tarski(A_51,B_52)) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_26])).

tff(c_56,plain,(
    ! [A_22,B_23] : k2_xboole_0(k1_tarski(A_22),k1_tarski(B_23)) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_66,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_16,plain,(
    ! [A_5,C_7,B_6] :
      ( r2_hidden(A_5,C_7)
      | ~ r2_hidden(A_5,B_6)
      | r2_hidden(A_5,k5_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_8,B_9] : k5_xboole_0(k5_xboole_0(A_8,B_9),k2_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_233,plain,(
    ! [A_77,C_78,B_79] :
      ( ~ r2_hidden(A_77,C_78)
      | ~ r2_hidden(A_77,B_79)
      | ~ r2_hidden(A_77,k5_xboole_0(B_79,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_657,plain,(
    ! [A_127,A_128,B_129] :
      ( ~ r2_hidden(A_127,k2_xboole_0(A_128,B_129))
      | ~ r2_hidden(A_127,k5_xboole_0(A_128,B_129))
      | ~ r2_hidden(A_127,k3_xboole_0(A_128,B_129)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_233])).

tff(c_6104,plain,(
    ! [A_9180,B_9181,C_9182] :
      ( ~ r2_hidden(A_9180,k2_xboole_0(B_9181,C_9182))
      | ~ r2_hidden(A_9180,k3_xboole_0(B_9181,C_9182))
      | r2_hidden(A_9180,C_9182)
      | ~ r2_hidden(A_9180,B_9181) ) ),
    inference(resolution,[status(thm)],[c_16,c_657])).

tff(c_6153,plain,(
    ! [A_9180] :
      ( ~ r2_hidden(A_9180,k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')))
      | ~ r2_hidden(A_9180,k1_tarski('#skF_6'))
      | r2_hidden(A_9180,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_9180,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_6104])).

tff(c_12108,plain,(
    ! [A_30399] :
      ( ~ r2_hidden(A_30399,k2_tarski('#skF_6','#skF_7'))
      | ~ r2_hidden(A_30399,k1_tarski('#skF_6'))
      | r2_hidden(A_30399,k1_tarski('#skF_7'))
      | ~ r2_hidden(A_30399,k1_tarski('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_6153])).

tff(c_12175,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_141,c_12108])).

tff(c_12193,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_12175])).

tff(c_44,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12206,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_12193,c_44])).

tff(c_12247,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_12206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:49:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.53/2.83  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.83  
% 8.53/2.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.83  %$ r2_hidden > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_5 > #skF_4
% 8.53/2.83  
% 8.53/2.83  %Foreground sorts:
% 8.53/2.83  
% 8.53/2.83  
% 8.53/2.83  %Background operators:
% 8.53/2.83  
% 8.53/2.83  
% 8.53/2.83  %Foreground operators:
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.53/2.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.53/2.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 8.53/2.83  tff('#skF_1', type, '#skF_1': $i > $i).
% 8.53/2.83  tff('#skF_7', type, '#skF_7': $i).
% 8.53/2.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 8.53/2.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 8.53/2.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 8.53/2.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 8.53/2.83  tff('#skF_6', type, '#skF_6': $i).
% 8.53/2.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.53/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.53/2.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 8.53/2.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 8.53/2.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 8.53/2.83  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 8.53/2.83  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 8.53/2.83  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 8.53/2.83  
% 8.53/2.84  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 8.53/2.84  tff(f_62, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 8.53/2.84  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 8.53/2.84  tff(f_55, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 8.53/2.84  tff(f_64, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 8.53/2.84  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 8.53/2.84  tff(f_40, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 8.53/2.84  tff(c_64, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.84  tff(c_46, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.84  tff(c_135, plain, (![A_51, B_52]: (k1_enumset1(A_51, A_51, B_52)=k2_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_68])).
% 8.53/2.84  tff(c_26, plain, (![E_16, B_11, C_12]: (r2_hidden(E_16, k1_enumset1(E_16, B_11, C_12)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.53/2.84  tff(c_141, plain, (![A_51, B_52]: (r2_hidden(A_51, k2_tarski(A_51, B_52)))), inference(superposition, [status(thm), theory('equality')], [c_135, c_26])).
% 8.53/2.84  tff(c_56, plain, (![A_22, B_23]: (k2_xboole_0(k1_tarski(A_22), k1_tarski(B_23))=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_64])).
% 8.53/2.84  tff(c_66, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_75])).
% 8.53/2.84  tff(c_16, plain, (![A_5, C_7, B_6]: (r2_hidden(A_5, C_7) | ~r2_hidden(A_5, B_6) | r2_hidden(A_5, k5_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.84  tff(c_18, plain, (![A_8, B_9]: (k5_xboole_0(k5_xboole_0(A_8, B_9), k2_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 8.53/2.84  tff(c_233, plain, (![A_77, C_78, B_79]: (~r2_hidden(A_77, C_78) | ~r2_hidden(A_77, B_79) | ~r2_hidden(A_77, k5_xboole_0(B_79, C_78)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 8.53/2.84  tff(c_657, plain, (![A_127, A_128, B_129]: (~r2_hidden(A_127, k2_xboole_0(A_128, B_129)) | ~r2_hidden(A_127, k5_xboole_0(A_128, B_129)) | ~r2_hidden(A_127, k3_xboole_0(A_128, B_129)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_233])).
% 8.53/2.84  tff(c_6104, plain, (![A_9180, B_9181, C_9182]: (~r2_hidden(A_9180, k2_xboole_0(B_9181, C_9182)) | ~r2_hidden(A_9180, k3_xboole_0(B_9181, C_9182)) | r2_hidden(A_9180, C_9182) | ~r2_hidden(A_9180, B_9181))), inference(resolution, [status(thm)], [c_16, c_657])).
% 8.53/2.84  tff(c_6153, plain, (![A_9180]: (~r2_hidden(A_9180, k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))) | ~r2_hidden(A_9180, k1_tarski('#skF_6')) | r2_hidden(A_9180, k1_tarski('#skF_7')) | ~r2_hidden(A_9180, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_66, c_6104])).
% 8.53/2.84  tff(c_12108, plain, (![A_30399]: (~r2_hidden(A_30399, k2_tarski('#skF_6', '#skF_7')) | ~r2_hidden(A_30399, k1_tarski('#skF_6')) | r2_hidden(A_30399, k1_tarski('#skF_7')) | ~r2_hidden(A_30399, k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_6153])).
% 8.53/2.84  tff(c_12175, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7')) | ~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_141, c_12108])).
% 8.53/2.84  tff(c_12193, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_12175])).
% 8.53/2.84  tff(c_44, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 8.53/2.84  tff(c_12206, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_12193, c_44])).
% 8.53/2.84  tff(c_12247, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_12206])).
% 8.53/2.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 8.53/2.84  
% 8.53/2.84  Inference rules
% 8.53/2.84  ----------------------
% 8.53/2.84  #Ref     : 0
% 8.53/2.84  #Sup     : 1450
% 8.53/2.84  #Fact    : 36
% 8.53/2.84  #Define  : 0
% 8.53/2.84  #Split   : 6
% 8.53/2.84  #Chain   : 0
% 8.53/2.84  #Close   : 0
% 8.53/2.84  
% 8.53/2.84  Ordering : KBO
% 8.53/2.84  
% 8.53/2.84  Simplification rules
% 8.53/2.84  ----------------------
% 8.53/2.84  #Subsume      : 346
% 8.53/2.84  #Demod        : 455
% 8.53/2.84  #Tautology    : 294
% 8.53/2.84  #SimpNegUnit  : 27
% 8.53/2.84  #BackRed      : 1
% 8.53/2.84  
% 8.53/2.84  #Partial instantiations: 12908
% 8.53/2.84  #Strategies tried      : 1
% 8.53/2.84  
% 8.53/2.84  Timing (in seconds)
% 8.53/2.84  ----------------------
% 8.53/2.85  Preprocessing        : 0.30
% 8.53/2.85  Parsing              : 0.15
% 8.53/2.85  CNF conversion       : 0.03
% 8.53/2.85  Main loop            : 1.77
% 8.53/2.85  Inferencing          : 0.93
% 8.53/2.85  Reduction            : 0.35
% 8.53/2.85  Demodulation         : 0.24
% 8.53/2.85  BG Simplification    : 0.07
% 8.53/2.85  Subsumption          : 0.33
% 8.53/2.85  Abstraction          : 0.09
% 8.53/2.85  MUC search           : 0.00
% 8.53/2.85  Cooper               : 0.00
% 8.53/2.85  Total                : 2.09
% 8.53/2.85  Index Insertion      : 0.00
% 8.53/2.85  Index Deletion       : 0.00
% 8.53/2.85  Index Matching       : 0.00
% 8.53/2.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------
