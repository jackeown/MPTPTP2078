%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:02 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   18 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_23,plain,(
    ! [B_16,A_17] :
      ( r1_xboole_0(B_16,A_17)
      | ~ r1_xboole_0(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_26,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_23])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k4_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_64,plain,(
    ! [A_20,B_21] :
      ( k2_xboole_0(A_20,B_21) = B_21
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),A_7) = A_7 ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_147,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_xboole_0(A_35,B_36)
      | ~ r1_xboole_0(A_35,k2_xboole_0(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_210,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_xboole_0(A_43,k4_xboole_0(A_44,B_45))
      | ~ r1_xboole_0(A_43,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_147])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_231,plain,(
    ! [A_49,B_50,A_51] :
      ( r1_xboole_0(k4_xboole_0(A_49,B_50),A_51)
      | ~ r1_xboole_0(A_51,A_49) ) ),
    inference(resolution,[status(thm)],[c_210,c_4])).

tff(c_294,plain,(
    ! [A_57,B_58,A_59] :
      ( r1_xboole_0(k3_xboole_0(A_57,B_58),A_59)
      | ~ r1_xboole_0(A_59,A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_231])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_82,plain,(
    ! [A_27,B_28] : k4_xboole_0(A_27,k4_xboole_0(A_27,B_28)) = k3_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [A_29,B_30] : r1_tarski(k3_xboole_0(A_29,B_30),A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8])).

tff(c_114,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_103])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_154,plain,(
    ! [B_38,A_39] : k2_xboole_0(k3_xboole_0(B_38,A_39),A_39) = A_39 ),
    inference(resolution,[status(thm)],[c_114,c_6])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( r1_xboole_0(A_11,B_12)
      | ~ r1_xboole_0(A_11,k2_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_280,plain,(
    ! [A_54,B_55,A_56] :
      ( r1_xboole_0(A_54,k3_xboole_0(B_55,A_56))
      | ~ r1_xboole_0(A_54,A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_21,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_292,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_280,c_21])).

tff(c_297,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_294,c_292])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:28:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.25  
% 1.98/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.25  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.10/1.25  
% 2.10/1.25  %Foreground sorts:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Background operators:
% 2.10/1.25  
% 2.10/1.25  
% 2.10/1.25  %Foreground operators:
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.10/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.10/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.10/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.10/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.10/1.25  
% 2.10/1.26  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.10/1.26  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.10/1.26  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.10/1.26  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.10/1.26  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.10/1.26  tff(f_55, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.10/1.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.10/1.26  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.26  tff(c_23, plain, (![B_16, A_17]: (r1_xboole_0(B_16, A_17) | ~r1_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.26  tff(c_26, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_23])).
% 2.10/1.26  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.26  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k4_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.10/1.26  tff(c_64, plain, (![A_20, B_21]: (k2_xboole_0(A_20, B_21)=B_21 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.26  tff(c_68, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), A_7)=A_7)), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.10/1.26  tff(c_147, plain, (![A_35, B_36, C_37]: (r1_xboole_0(A_35, B_36) | ~r1_xboole_0(A_35, k2_xboole_0(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.26  tff(c_210, plain, (![A_43, A_44, B_45]: (r1_xboole_0(A_43, k4_xboole_0(A_44, B_45)) | ~r1_xboole_0(A_43, A_44))), inference(superposition, [status(thm), theory('equality')], [c_68, c_147])).
% 2.10/1.26  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.10/1.26  tff(c_231, plain, (![A_49, B_50, A_51]: (r1_xboole_0(k4_xboole_0(A_49, B_50), A_51) | ~r1_xboole_0(A_51, A_49))), inference(resolution, [status(thm)], [c_210, c_4])).
% 2.10/1.26  tff(c_294, plain, (![A_57, B_58, A_59]: (r1_xboole_0(k3_xboole_0(A_57, B_58), A_59) | ~r1_xboole_0(A_59, A_57))), inference(superposition, [status(thm), theory('equality')], [c_10, c_231])).
% 2.10/1.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.10/1.26  tff(c_82, plain, (![A_27, B_28]: (k4_xboole_0(A_27, k4_xboole_0(A_27, B_28))=k3_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.10/1.26  tff(c_103, plain, (![A_29, B_30]: (r1_tarski(k3_xboole_0(A_29, B_30), A_29))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8])).
% 2.10/1.26  tff(c_114, plain, (![B_31, A_32]: (r1_tarski(k3_xboole_0(B_31, A_32), A_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_103])).
% 2.10/1.26  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.10/1.26  tff(c_154, plain, (![B_38, A_39]: (k2_xboole_0(k3_xboole_0(B_38, A_39), A_39)=A_39)), inference(resolution, [status(thm)], [c_114, c_6])).
% 2.10/1.26  tff(c_16, plain, (![A_11, B_12, C_13]: (r1_xboole_0(A_11, B_12) | ~r1_xboole_0(A_11, k2_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.10/1.26  tff(c_280, plain, (![A_54, B_55, A_56]: (r1_xboole_0(A_54, k3_xboole_0(B_55, A_56)) | ~r1_xboole_0(A_54, A_56))), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 2.10/1.26  tff(c_18, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.10/1.26  tff(c_21, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 2.10/1.26  tff(c_292, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_280, c_21])).
% 2.10/1.26  tff(c_297, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_294, c_292])).
% 2.10/1.26  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_297])).
% 2.10/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.26  
% 2.10/1.26  Inference rules
% 2.10/1.26  ----------------------
% 2.10/1.26  #Ref     : 0
% 2.10/1.26  #Sup     : 78
% 2.10/1.26  #Fact    : 0
% 2.10/1.26  #Define  : 0
% 2.10/1.26  #Split   : 0
% 2.10/1.26  #Chain   : 0
% 2.10/1.26  #Close   : 0
% 2.10/1.26  
% 2.10/1.26  Ordering : KBO
% 2.10/1.27  
% 2.10/1.27  Simplification rules
% 2.10/1.27  ----------------------
% 2.10/1.27  #Subsume      : 5
% 2.10/1.27  #Demod        : 13
% 2.10/1.27  #Tautology    : 39
% 2.10/1.27  #SimpNegUnit  : 0
% 2.10/1.27  #BackRed      : 0
% 2.10/1.27  
% 2.10/1.27  #Partial instantiations: 0
% 2.10/1.27  #Strategies tried      : 1
% 2.10/1.27  
% 2.10/1.27  Timing (in seconds)
% 2.10/1.27  ----------------------
% 2.10/1.27  Preprocessing        : 0.25
% 2.10/1.27  Parsing              : 0.13
% 2.10/1.27  CNF conversion       : 0.02
% 2.10/1.27  Main loop            : 0.21
% 2.10/1.27  Inferencing          : 0.08
% 2.10/1.27  Reduction            : 0.07
% 2.10/1.27  Demodulation         : 0.06
% 2.10/1.27  BG Simplification    : 0.01
% 2.10/1.27  Subsumption          : 0.04
% 2.10/1.27  Abstraction          : 0.01
% 2.10/1.27  MUC search           : 0.00
% 2.10/1.27  Cooper               : 0.00
% 2.10/1.27  Total                : 0.49
% 2.10/1.27  Index Insertion      : 0.00
% 2.10/1.27  Index Deletion       : 0.00
% 2.10/1.27  Index Matching       : 0.00
% 2.10/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
