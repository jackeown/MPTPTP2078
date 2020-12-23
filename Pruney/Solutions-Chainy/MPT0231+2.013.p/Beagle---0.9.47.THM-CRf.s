%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:16 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  40 expanded)
%              Number of equality atoms :   16 (  19 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_20,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k1_tarski(A_18),k2_tarski(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_79,plain,(
    ! [A_31,B_32] :
      ( k3_xboole_0(A_31,B_32) = A_31
      | ~ r1_tarski(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_18,B_19] : k3_xboole_0(k1_tarski(A_18),k2_tarski(A_18,B_19)) = k1_tarski(A_18) ),
    inference(resolution,[status(thm)],[c_16,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_117,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(k3_xboole_0(A_34,C_35),B_36)
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_150,plain,(
    ! [B_39,A_40,B_41] :
      ( r1_tarski(k3_xboole_0(B_39,A_40),B_41)
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_117])).

tff(c_194,plain,(
    ! [A_50,B_51,B_52] :
      ( r1_tarski(k1_tarski(A_50),B_51)
      | ~ r1_tarski(k2_tarski(A_50,B_52),B_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_150])).

tff(c_201,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_194])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_179,plain,(
    ! [C_45,A_46,B_47] :
      ( C_45 = A_46
      | B_47 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k2_tarski(B_47,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_185,plain,(
    ! [A_8,A_46] :
      ( A_8 = A_46
      | A_8 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_179])).

tff(c_204,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_201,c_185])).

tff(c_211,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_20,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:29:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.32  
% 1.76/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.32  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.76/1.32  
% 1.76/1.32  %Foreground sorts:
% 1.76/1.32  
% 1.76/1.32  
% 1.76/1.32  %Background operators:
% 1.76/1.32  
% 1.76/1.32  
% 1.76/1.32  %Foreground operators:
% 1.76/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.76/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.32  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.32  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.32  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.32  
% 1.92/1.33  tff(f_59, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.92/1.33  tff(f_45, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.92/1.33  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.92/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.92/1.33  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 1.92/1.33  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.33  tff(f_54, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.92/1.33  tff(c_20, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.33  tff(c_22, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.33  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k1_tarski(A_18), k2_tarski(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.92/1.33  tff(c_79, plain, (![A_31, B_32]: (k3_xboole_0(A_31, B_32)=A_31 | ~r1_tarski(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.33  tff(c_90, plain, (![A_18, B_19]: (k3_xboole_0(k1_tarski(A_18), k2_tarski(A_18, B_19))=k1_tarski(A_18))), inference(resolution, [status(thm)], [c_16, c_79])).
% 1.92/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.33  tff(c_117, plain, (![A_34, C_35, B_36]: (r1_tarski(k3_xboole_0(A_34, C_35), B_36) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.33  tff(c_150, plain, (![B_39, A_40, B_41]: (r1_tarski(k3_xboole_0(B_39, A_40), B_41) | ~r1_tarski(A_40, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_117])).
% 1.92/1.33  tff(c_194, plain, (![A_50, B_51, B_52]: (r1_tarski(k1_tarski(A_50), B_51) | ~r1_tarski(k2_tarski(A_50, B_52), B_51))), inference(superposition, [status(thm), theory('equality')], [c_90, c_150])).
% 1.92/1.33  tff(c_201, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_22, c_194])).
% 1.92/1.33  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.33  tff(c_179, plain, (![C_45, A_46, B_47]: (C_45=A_46 | B_47=A_46 | ~r1_tarski(k1_tarski(A_46), k2_tarski(B_47, C_45)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.33  tff(c_185, plain, (![A_8, A_46]: (A_8=A_46 | A_8=A_46 | ~r1_tarski(k1_tarski(A_46), k1_tarski(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_179])).
% 1.92/1.33  tff(c_204, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_201, c_185])).
% 1.92/1.33  tff(c_211, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_20, c_204])).
% 1.92/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.33  
% 1.92/1.33  Inference rules
% 1.92/1.33  ----------------------
% 1.92/1.33  #Ref     : 0
% 1.92/1.33  #Sup     : 48
% 1.92/1.33  #Fact    : 0
% 1.92/1.33  #Define  : 0
% 1.92/1.33  #Split   : 0
% 1.92/1.33  #Chain   : 0
% 1.92/1.33  #Close   : 0
% 1.92/1.33  
% 1.92/1.33  Ordering : KBO
% 1.92/1.33  
% 1.92/1.33  Simplification rules
% 1.92/1.33  ----------------------
% 1.92/1.33  #Subsume      : 3
% 1.92/1.33  #Demod        : 1
% 1.92/1.33  #Tautology    : 28
% 1.92/1.33  #SimpNegUnit  : 1
% 1.92/1.33  #BackRed      : 0
% 1.92/1.33  
% 1.92/1.33  #Partial instantiations: 0
% 1.92/1.33  #Strategies tried      : 1
% 1.92/1.33  
% 1.92/1.33  Timing (in seconds)
% 1.92/1.33  ----------------------
% 1.92/1.33  Preprocessing        : 0.31
% 1.92/1.33  Parsing              : 0.16
% 1.92/1.33  CNF conversion       : 0.02
% 1.92/1.33  Main loop            : 0.15
% 1.92/1.33  Inferencing          : 0.06
% 1.92/1.33  Reduction            : 0.05
% 1.92/1.33  Demodulation         : 0.04
% 1.92/1.33  BG Simplification    : 0.01
% 1.92/1.33  Subsumption          : 0.02
% 1.92/1.33  Abstraction          : 0.01
% 1.92/1.33  MUC search           : 0.00
% 1.92/1.33  Cooper               : 0.00
% 1.92/1.33  Total                : 0.48
% 1.92/1.33  Index Insertion      : 0.00
% 1.92/1.33  Index Deletion       : 0.00
% 1.92/1.33  Index Matching       : 0.00
% 1.92/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
