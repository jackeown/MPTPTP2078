%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_14,B_15] : r1_tarski(k1_tarski(A_14),k2_tarski(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_70,plain,(
    ! [A_25,B_26] :
      ( k2_xboole_0(A_25,B_26) = B_26
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) = k2_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_70])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_105,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,k2_xboole_0(C_31,B_32))
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_122,plain,(
    ! [A_33,B_34,A_35] :
      ( r1_tarski(A_33,k2_xboole_0(B_34,A_35))
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_105])).

tff(c_195,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_49,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_122])).

tff(c_16,plain,(
    ! [C_18,A_16,B_17] :
      ( C_18 = A_16
      | B_17 = A_16
      | ~ r1_tarski(k1_tarski(A_16),k2_tarski(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_210,plain,(
    ! [A_53] :
      ( A_53 = '#skF_4'
      | A_53 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_53),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_195,c_16])).

tff(c_217,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_210])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:04:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.28  
% 1.92/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.28  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.92/1.28  
% 1.92/1.28  %Foreground sorts:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Background operators:
% 1.92/1.28  
% 1.92/1.28  
% 1.92/1.28  %Foreground operators:
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.92/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.28  
% 1.92/1.29  tff(f_62, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 1.92/1.29  tff(f_43, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.92/1.29  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.92/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.29  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.92/1.29  tff(f_52, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.92/1.29  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.29  tff(c_18, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.29  tff(c_14, plain, (![A_14, B_15]: (r1_tarski(k1_tarski(A_14), k2_tarski(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.29  tff(c_22, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.92/1.29  tff(c_70, plain, (![A_25, B_26]: (k2_xboole_0(A_25, B_26)=B_26 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.29  tff(c_80, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))=k2_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_70])).
% 1.92/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.29  tff(c_105, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, k2_xboole_0(C_31, B_32)) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.29  tff(c_122, plain, (![A_33, B_34, A_35]: (r1_tarski(A_33, k2_xboole_0(B_34, A_35)) | ~r1_tarski(A_33, B_34))), inference(superposition, [status(thm), theory('equality')], [c_2, c_105])).
% 1.92/1.29  tff(c_195, plain, (![A_49]: (r1_tarski(A_49, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_49, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_80, c_122])).
% 1.92/1.29  tff(c_16, plain, (![C_18, A_16, B_17]: (C_18=A_16 | B_17=A_16 | ~r1_tarski(k1_tarski(A_16), k2_tarski(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.29  tff(c_210, plain, (![A_53]: (A_53='#skF_4' | A_53='#skF_3' | ~r1_tarski(k1_tarski(A_53), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_195, c_16])).
% 1.92/1.29  tff(c_217, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_14, c_210])).
% 1.92/1.29  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_217])).
% 1.92/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.29  
% 1.92/1.29  Inference rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Ref     : 0
% 1.92/1.29  #Sup     : 48
% 1.92/1.29  #Fact    : 0
% 1.92/1.29  #Define  : 0
% 1.92/1.29  #Split   : 0
% 1.92/1.29  #Chain   : 0
% 1.92/1.29  #Close   : 0
% 1.92/1.29  
% 1.92/1.29  Ordering : KBO
% 1.92/1.29  
% 1.92/1.29  Simplification rules
% 1.92/1.29  ----------------------
% 1.92/1.29  #Subsume      : 4
% 1.92/1.29  #Demod        : 2
% 1.92/1.29  #Tautology    : 29
% 1.92/1.29  #SimpNegUnit  : 1
% 1.92/1.29  #BackRed      : 0
% 1.92/1.29  
% 1.92/1.29  #Partial instantiations: 0
% 1.92/1.29  #Strategies tried      : 1
% 1.92/1.29  
% 1.92/1.29  Timing (in seconds)
% 1.92/1.29  ----------------------
% 1.92/1.30  Preprocessing        : 0.33
% 1.92/1.30  Parsing              : 0.16
% 1.92/1.30  CNF conversion       : 0.02
% 1.92/1.30  Main loop            : 0.18
% 1.92/1.30  Inferencing          : 0.07
% 1.92/1.30  Reduction            : 0.05
% 1.92/1.30  Demodulation         : 0.04
% 1.92/1.30  BG Simplification    : 0.02
% 2.11/1.30  Subsumption          : 0.03
% 2.11/1.30  Abstraction          : 0.01
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.54
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
