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
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   31 (  39 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :    5 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_18,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    ! [B_12,A_13] :
      ( r1_xboole_0(B_12,A_13)
      | ~ r1_xboole_0(A_13,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_23,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_18,c_20])).

tff(c_77,plain,(
    ! [A_21,B_22] : k2_xboole_0(k3_xboole_0(A_21,B_22),k4_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_9,B_10,C_11] :
      ( r1_xboole_0(A_9,B_10)
      | ~ r1_xboole_0(A_9,k2_xboole_0(B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_117,plain,(
    ! [A_29,A_30,B_31] :
      ( r1_xboole_0(A_29,k3_xboole_0(A_30,B_31))
      | ~ r1_xboole_0(A_29,A_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_14])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_130,plain,(
    ! [A_30,B_31,A_29] :
      ( r1_xboole_0(k3_xboole_0(A_30,B_31),A_29)
      | ~ r1_xboole_0(A_29,A_30) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_131,plain,(
    ! [B_32,A_33] : k2_xboole_0(k3_xboole_0(B_32,A_33),k4_xboole_0(A_33,B_32)) = A_33 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_77])).

tff(c_239,plain,(
    ! [A_42,B_43,A_44] :
      ( r1_xboole_0(A_42,k3_xboole_0(B_43,A_44))
      | ~ r1_xboole_0(A_42,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_14])).

tff(c_16,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_19,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_16])).

tff(c_251,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_239,c_19])).

tff(c_255,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_130,c_251])).

tff(c_259,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_255])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:45:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.22  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.03/1.22  
% 2.03/1.22  %Foreground sorts:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Background operators:
% 2.03/1.22  
% 2.03/1.22  
% 2.03/1.22  %Foreground operators:
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.03/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.03/1.22  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.22  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.03/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.03/1.22  
% 2.03/1.23  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.03/1.23  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.03/1.23  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.03/1.23  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.03/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.03/1.23  tff(c_18, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.23  tff(c_20, plain, (![B_12, A_13]: (r1_xboole_0(B_12, A_13) | ~r1_xboole_0(A_13, B_12))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.23  tff(c_23, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_18, c_20])).
% 2.03/1.23  tff(c_77, plain, (![A_21, B_22]: (k2_xboole_0(k3_xboole_0(A_21, B_22), k4_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.23  tff(c_14, plain, (![A_9, B_10, C_11]: (r1_xboole_0(A_9, B_10) | ~r1_xboole_0(A_9, k2_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.03/1.23  tff(c_117, plain, (![A_29, A_30, B_31]: (r1_xboole_0(A_29, k3_xboole_0(A_30, B_31)) | ~r1_xboole_0(A_29, A_30))), inference(superposition, [status(thm), theory('equality')], [c_77, c_14])).
% 2.03/1.23  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.03/1.23  tff(c_130, plain, (![A_30, B_31, A_29]: (r1_xboole_0(k3_xboole_0(A_30, B_31), A_29) | ~r1_xboole_0(A_29, A_30))), inference(resolution, [status(thm)], [c_117, c_4])).
% 2.03/1.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.03/1.23  tff(c_131, plain, (![B_32, A_33]: (k2_xboole_0(k3_xboole_0(B_32, A_33), k4_xboole_0(A_33, B_32))=A_33)), inference(superposition, [status(thm), theory('equality')], [c_2, c_77])).
% 2.03/1.23  tff(c_239, plain, (![A_42, B_43, A_44]: (r1_xboole_0(A_42, k3_xboole_0(B_43, A_44)) | ~r1_xboole_0(A_42, A_44))), inference(superposition, [status(thm), theory('equality')], [c_131, c_14])).
% 2.03/1.23  tff(c_16, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.03/1.23  tff(c_19, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_16])).
% 2.03/1.23  tff(c_251, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_239, c_19])).
% 2.03/1.23  tff(c_255, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_130, c_251])).
% 2.03/1.23  tff(c_259, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_23, c_255])).
% 2.03/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.03/1.23  
% 2.03/1.23  Inference rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Ref     : 0
% 2.03/1.23  #Sup     : 62
% 2.03/1.23  #Fact    : 0
% 2.03/1.23  #Define  : 0
% 2.03/1.23  #Split   : 0
% 2.03/1.23  #Chain   : 0
% 2.03/1.23  #Close   : 0
% 2.03/1.23  
% 2.03/1.23  Ordering : KBO
% 2.03/1.23  
% 2.03/1.23  Simplification rules
% 2.03/1.23  ----------------------
% 2.03/1.23  #Subsume      : 5
% 2.03/1.23  #Demod        : 8
% 2.03/1.23  #Tautology    : 24
% 2.03/1.23  #SimpNegUnit  : 0
% 2.03/1.23  #BackRed      : 0
% 2.03/1.23  
% 2.03/1.23  #Partial instantiations: 0
% 2.03/1.23  #Strategies tried      : 1
% 2.03/1.23  
% 2.03/1.23  Timing (in seconds)
% 2.03/1.23  ----------------------
% 2.03/1.23  Preprocessing        : 0.27
% 2.03/1.23  Parsing              : 0.15
% 2.03/1.23  CNF conversion       : 0.02
% 2.03/1.23  Main loop            : 0.21
% 2.03/1.23  Inferencing          : 0.08
% 2.03/1.23  Reduction            : 0.07
% 2.03/1.23  Demodulation         : 0.06
% 2.03/1.23  BG Simplification    : 0.01
% 2.03/1.23  Subsumption          : 0.04
% 2.03/1.23  Abstraction          : 0.01
% 2.03/1.23  MUC search           : 0.00
% 2.03/1.23  Cooper               : 0.00
% 2.03/1.23  Total                : 0.50
% 2.03/1.23  Index Insertion      : 0.00
% 2.03/1.23  Index Deletion       : 0.00
% 2.03/1.23  Index Matching       : 0.00
% 2.03/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
