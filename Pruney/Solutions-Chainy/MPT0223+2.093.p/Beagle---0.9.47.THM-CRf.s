%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   34 (  41 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  48 expanded)
%              Number of equality atoms :   10 (  15 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_16,plain,(
    ! [B_17] : ~ r1_xboole_0(k1_tarski(B_17),k1_tarski(B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_110,plain,(
    ! [A_38,B_39] :
      ( r2_hidden('#skF_1'(A_38,B_39),k3_xboole_0(A_38,B_39))
      | r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_123,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40,A_40),A_40)
      | r1_xboole_0(A_40,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_110])).

tff(c_20,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_18,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(k1_tarski(A_18),k1_tarski(B_19))
      | B_19 = A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_77,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [C_31] :
      ( ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3'))
      | ~ r2_hidden(C_31,k1_tarski('#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_77])).

tff(c_84,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_87,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_87])).

tff(c_92,plain,(
    ! [C_31] : ~ r2_hidden(C_31,k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_127,plain,(
    r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_123,c_92])).

tff(c_135,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:48:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.18  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.79/1.18  
% 1.79/1.18  %Foreground sorts:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Background operators:
% 1.79/1.18  
% 1.79/1.18  
% 1.79/1.18  %Foreground operators:
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.79/1.18  
% 1.85/1.19  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.85/1.19  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 1.85/1.19  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.85/1.19  tff(f_64, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.85/1.19  tff(f_59, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.85/1.19  tff(c_16, plain, (![B_17]: (~r1_xboole_0(k1_tarski(B_17), k1_tarski(B_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.19  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.19  tff(c_110, plain, (![A_38, B_39]: (r2_hidden('#skF_1'(A_38, B_39), k3_xboole_0(A_38, B_39)) | r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.19  tff(c_123, plain, (![A_40]: (r2_hidden('#skF_1'(A_40, A_40), A_40) | r1_xboole_0(A_40, A_40))), inference(superposition, [status(thm), theory('equality')], [c_2, c_110])).
% 1.85/1.19  tff(c_20, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.19  tff(c_18, plain, (![A_18, B_19]: (r1_xboole_0(k1_tarski(A_18), k1_tarski(B_19)) | B_19=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.85/1.19  tff(c_22, plain, (k3_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.85/1.19  tff(c_77, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.19  tff(c_80, plain, (![C_31]: (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3')) | ~r2_hidden(C_31, k1_tarski('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_77])).
% 1.85/1.19  tff(c_84, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.85/1.19  tff(c_87, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_18, c_84])).
% 1.85/1.19  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_87])).
% 1.85/1.19  tff(c_92, plain, (![C_31]: (~r2_hidden(C_31, k1_tarski('#skF_2')))), inference(splitRight, [status(thm)], [c_80])).
% 1.85/1.19  tff(c_127, plain, (r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_123, c_92])).
% 1.85/1.19  tff(c_135, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_127])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 24
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 1
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 0
% 1.85/1.19  #Demod        : 1
% 1.85/1.19  #Tautology    : 16
% 1.85/1.19  #SimpNegUnit  : 3
% 1.85/1.19  #BackRed      : 0
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.19  Preprocessing        : 0.29
% 1.85/1.19  Parsing              : 0.16
% 1.85/1.19  CNF conversion       : 0.02
% 1.85/1.19  Main loop            : 0.11
% 1.85/1.19  Inferencing          : 0.05
% 1.85/1.19  Reduction            : 0.03
% 1.85/1.19  Demodulation         : 0.02
% 1.85/1.19  BG Simplification    : 0.01
% 1.85/1.19  Subsumption          : 0.02
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.43
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.19  Index Deletion       : 0.00
% 1.85/1.19  Index Matching       : 0.00
% 1.85/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
