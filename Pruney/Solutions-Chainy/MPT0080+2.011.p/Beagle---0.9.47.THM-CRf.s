%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:51 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  56 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(c_18,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [B_18,A_19] : k2_xboole_0(B_18,A_19) = k2_xboole_0(A_19,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_59,plain,(
    ! [A_19] : k2_xboole_0(k1_xboole_0,A_19) = A_19 ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_10])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_378,plain,(
    ! [A_38,B_39] :
      ( k3_xboole_0(A_38,B_39) = k1_xboole_0
      | ~ r1_xboole_0(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_386,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_378])).

tff(c_391,plain,(
    ! [A_40,B_41,C_42] : k2_xboole_0(k3_xboole_0(A_40,B_41),k3_xboole_0(A_40,C_42)) = k3_xboole_0(A_40,k2_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_418,plain,(
    ! [C_42] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_42)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_391])).

tff(c_1205,plain,(
    ! [C_62] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_62)) = k3_xboole_0('#skF_1',C_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_418])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_23,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_186,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_23,c_186])).

tff(c_1252,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_206])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [B_18,A_19] : r1_tarski(B_18,k2_xboole_0(A_19,B_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_16])).

tff(c_202,plain,(
    ! [B_18,A_19] : k3_xboole_0(B_18,k2_xboole_0(A_19,B_18)) = B_18 ),
    inference(resolution,[status(thm)],[c_55,c_186])).

tff(c_609,plain,(
    ! [A_46,B_47,C_48] : r1_tarski(k3_xboole_0(A_46,B_47),k3_xboole_0(A_46,k2_xboole_0(B_47,C_48))) ),
    inference(superposition,[status(thm),theory(equality)],[c_391,c_16])).

tff(c_700,plain,(
    ! [B_49,A_50] : r1_tarski(k3_xboole_0(B_49,A_50),B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_609])).

tff(c_727,plain,(
    ! [B_4,A_3] : r1_tarski(k3_xboole_0(B_4,A_3),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_700])).

tff(c_1326,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1252,c_727])).

tff(c_1348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_1326])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:41:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.39  %$ r1_xboole_0 > r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.84/1.39  
% 2.84/1.39  %Foreground sorts:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Background operators:
% 2.84/1.39  
% 2.84/1.39  
% 2.84/1.39  %Foreground operators:
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.39  
% 2.84/1.40  tff(f_50, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.84/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.84/1.40  tff(f_35, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.84/1.40  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.84/1.40  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.84/1.40  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.84/1.40  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.84/1.40  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.84/1.40  tff(c_18, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.40  tff(c_37, plain, (![B_18, A_19]: (k2_xboole_0(B_18, A_19)=k2_xboole_0(A_19, B_18))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.40  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.84/1.40  tff(c_59, plain, (![A_19]: (k2_xboole_0(k1_xboole_0, A_19)=A_19)), inference(superposition, [status(thm), theory('equality')], [c_37, c_10])).
% 2.84/1.40  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.40  tff(c_378, plain, (![A_38, B_39]: (k3_xboole_0(A_38, B_39)=k1_xboole_0 | ~r1_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.40  tff(c_386, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_378])).
% 2.84/1.40  tff(c_391, plain, (![A_40, B_41, C_42]: (k2_xboole_0(k3_xboole_0(A_40, B_41), k3_xboole_0(A_40, C_42))=k3_xboole_0(A_40, k2_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.84/1.40  tff(c_418, plain, (![C_42]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_42))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_42)))), inference(superposition, [status(thm), theory('equality')], [c_386, c_391])).
% 2.84/1.40  tff(c_1205, plain, (![C_62]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_62))=k3_xboole_0('#skF_1', C_62))), inference(demodulation, [status(thm), theory('equality')], [c_59, c_418])).
% 2.84/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.40  tff(c_22, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.84/1.40  tff(c_23, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 2.84/1.40  tff(c_186, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.40  tff(c_206, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_23, c_186])).
% 2.84/1.40  tff(c_1252, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1205, c_206])).
% 2.84/1.40  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.84/1.40  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.84/1.40  tff(c_55, plain, (![B_18, A_19]: (r1_tarski(B_18, k2_xboole_0(A_19, B_18)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_16])).
% 2.84/1.40  tff(c_202, plain, (![B_18, A_19]: (k3_xboole_0(B_18, k2_xboole_0(A_19, B_18))=B_18)), inference(resolution, [status(thm)], [c_55, c_186])).
% 2.84/1.40  tff(c_609, plain, (![A_46, B_47, C_48]: (r1_tarski(k3_xboole_0(A_46, B_47), k3_xboole_0(A_46, k2_xboole_0(B_47, C_48))))), inference(superposition, [status(thm), theory('equality')], [c_391, c_16])).
% 2.84/1.40  tff(c_700, plain, (![B_49, A_50]: (r1_tarski(k3_xboole_0(B_49, A_50), B_49))), inference(superposition, [status(thm), theory('equality')], [c_202, c_609])).
% 2.84/1.40  tff(c_727, plain, (![B_4, A_3]: (r1_tarski(k3_xboole_0(B_4, A_3), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_700])).
% 2.84/1.40  tff(c_1326, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1252, c_727])).
% 2.84/1.40  tff(c_1348, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_1326])).
% 2.84/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  Inference rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Ref     : 0
% 2.84/1.40  #Sup     : 326
% 2.84/1.40  #Fact    : 0
% 2.84/1.40  #Define  : 0
% 2.84/1.40  #Split   : 0
% 2.84/1.40  #Chain   : 0
% 2.84/1.40  #Close   : 0
% 2.84/1.40  
% 2.84/1.40  Ordering : KBO
% 2.84/1.40  
% 2.84/1.40  Simplification rules
% 2.84/1.40  ----------------------
% 2.84/1.40  #Subsume      : 0
% 2.84/1.40  #Demod        : 220
% 2.84/1.40  #Tautology    : 211
% 2.84/1.40  #SimpNegUnit  : 1
% 2.84/1.40  #BackRed      : 0
% 2.84/1.40  
% 2.84/1.40  #Partial instantiations: 0
% 2.84/1.40  #Strategies tried      : 1
% 2.84/1.40  
% 2.84/1.40  Timing (in seconds)
% 2.84/1.40  ----------------------
% 2.84/1.40  Preprocessing        : 0.25
% 2.84/1.40  Parsing              : 0.14
% 2.84/1.40  CNF conversion       : 0.02
% 2.84/1.40  Main loop            : 0.39
% 2.84/1.40  Inferencing          : 0.13
% 2.84/1.40  Reduction            : 0.17
% 2.84/1.40  Demodulation         : 0.14
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.05
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.67
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
