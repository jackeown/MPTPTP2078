%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:59 EST 2020

% Result     : Theorem 5.20s
% Output     : CNFRefutation 5.26s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  47 expanded)
%              Number of equality atoms :   30 (  41 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = B_8
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_145,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_149,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_145])).

tff(c_223,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_232,plain,(
    ! [A_37,B_38] : k5_xboole_0(k4_xboole_0(A_37,B_38),k3_xboole_0(A_37,B_38)) = k2_xboole_0(k4_xboole_0(A_37,B_38),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_20])).

tff(c_862,plain,(
    ! [A_64,B_65] : k5_xboole_0(k4_xboole_0(A_64,B_65),k3_xboole_0(A_64,B_65)) = A_64 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_232])).

tff(c_51,plain,(
    ! [B_24,A_25] : k5_xboole_0(B_24,A_25) = k5_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [A_25] : k5_xboole_0(k1_xboole_0,A_25) = A_25 ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_14])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_361,plain,(
    ! [A_49,B_50,C_51] : k5_xboole_0(k5_xboole_0(A_49,B_50),C_51) = k5_xboole_0(A_49,k5_xboole_0(B_50,C_51)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_425,plain,(
    ! [A_17,C_51] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_51)) = k5_xboole_0(k1_xboole_0,C_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_361])).

tff(c_438,plain,(
    ! [A_17,C_51] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_51)) = C_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_425])).

tff(c_1234,plain,(
    ! [A_75,B_76] : k5_xboole_0(k4_xboole_0(A_75,B_76),A_75) = k3_xboole_0(A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_862,c_438])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_439,plain,(
    ! [A_52,C_53] : k5_xboole_0(A_52,k5_xboole_0(A_52,C_53)) = C_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_425])).

tff(c_482,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_439])).

tff(c_1249,plain,(
    ! [A_75,B_76] : k5_xboole_0(A_75,k3_xboole_0(A_75,B_76)) = k4_xboole_0(A_75,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_1234,c_482])).

tff(c_22,plain,(
    k5_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) != k4_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_5311,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1249,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.20/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.20/1.99  
% 5.20/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/1.99  %$ r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 5.26/1.99  
% 5.26/1.99  %Foreground sorts:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Background operators:
% 5.26/1.99  
% 5.26/1.99  
% 5.26/1.99  %Foreground operators:
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.26/1.99  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.26/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.26/1.99  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.26/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.26/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.26/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.26/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.26/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.26/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.26/1.99  
% 5.26/2.00  tff(f_29, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 5.26/2.00  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.26/2.00  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 5.26/2.00  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.26/2.00  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.26/2.00  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 5.26/2.00  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.26/2.00  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 5.26/2.00  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.26/2.00  tff(f_50, negated_conjecture, ~(![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.26/2.00  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.26/2.00  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.26/2.00  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=B_8 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.26/2.00  tff(c_145, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 5.26/2.00  tff(c_149, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_145])).
% 5.26/2.00  tff(c_223, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.26/2.00  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.26/2.00  tff(c_232, plain, (![A_37, B_38]: (k5_xboole_0(k4_xboole_0(A_37, B_38), k3_xboole_0(A_37, B_38))=k2_xboole_0(k4_xboole_0(A_37, B_38), A_37))), inference(superposition, [status(thm), theory('equality')], [c_223, c_20])).
% 5.26/2.00  tff(c_862, plain, (![A_64, B_65]: (k5_xboole_0(k4_xboole_0(A_64, B_65), k3_xboole_0(A_64, B_65))=A_64)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_232])).
% 5.26/2.00  tff(c_51, plain, (![B_24, A_25]: (k5_xboole_0(B_24, A_25)=k5_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.00  tff(c_14, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.26/2.00  tff(c_67, plain, (![A_25]: (k5_xboole_0(k1_xboole_0, A_25)=A_25)), inference(superposition, [status(thm), theory('equality')], [c_51, c_14])).
% 5.26/2.00  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.26/2.00  tff(c_361, plain, (![A_49, B_50, C_51]: (k5_xboole_0(k5_xboole_0(A_49, B_50), C_51)=k5_xboole_0(A_49, k5_xboole_0(B_50, C_51)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.26/2.00  tff(c_425, plain, (![A_17, C_51]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_51))=k5_xboole_0(k1_xboole_0, C_51))), inference(superposition, [status(thm), theory('equality')], [c_18, c_361])).
% 5.26/2.00  tff(c_438, plain, (![A_17, C_51]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_51))=C_51)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_425])).
% 5.26/2.00  tff(c_1234, plain, (![A_75, B_76]: (k5_xboole_0(k4_xboole_0(A_75, B_76), A_75)=k3_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_862, c_438])).
% 5.26/2.00  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.26/2.00  tff(c_439, plain, (![A_52, C_53]: (k5_xboole_0(A_52, k5_xboole_0(A_52, C_53))=C_53)), inference(demodulation, [status(thm), theory('equality')], [c_67, c_425])).
% 5.26/2.00  tff(c_482, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_439])).
% 5.26/2.00  tff(c_1249, plain, (![A_75, B_76]: (k5_xboole_0(A_75, k3_xboole_0(A_75, B_76))=k4_xboole_0(A_75, B_76))), inference(superposition, [status(thm), theory('equality')], [c_1234, c_482])).
% 5.26/2.00  tff(c_22, plain, (k5_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))!=k4_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.26/2.00  tff(c_5311, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1249, c_22])).
% 5.26/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.26/2.00  
% 5.26/2.00  Inference rules
% 5.26/2.00  ----------------------
% 5.26/2.00  #Ref     : 0
% 5.26/2.00  #Sup     : 1345
% 5.26/2.00  #Fact    : 0
% 5.26/2.00  #Define  : 0
% 5.26/2.00  #Split   : 0
% 5.26/2.00  #Chain   : 0
% 5.26/2.00  #Close   : 0
% 5.26/2.00  
% 5.26/2.00  Ordering : KBO
% 5.26/2.00  
% 5.26/2.00  Simplification rules
% 5.26/2.00  ----------------------
% 5.26/2.00  #Subsume      : 30
% 5.26/2.00  #Demod        : 1357
% 5.26/2.00  #Tautology    : 756
% 5.26/2.00  #SimpNegUnit  : 0
% 5.26/2.00  #BackRed      : 1
% 5.26/2.00  
% 5.26/2.00  #Partial instantiations: 0
% 5.26/2.00  #Strategies tried      : 1
% 5.26/2.00  
% 5.26/2.00  Timing (in seconds)
% 5.26/2.00  ----------------------
% 5.26/2.00  Preprocessing        : 0.27
% 5.26/2.00  Parsing              : 0.15
% 5.26/2.00  CNF conversion       : 0.02
% 5.26/2.00  Main loop            : 0.97
% 5.26/2.00  Inferencing          : 0.30
% 5.26/2.00  Reduction            : 0.46
% 5.26/2.00  Demodulation         : 0.39
% 5.26/2.00  BG Simplification    : 0.04
% 5.26/2.00  Subsumption          : 0.12
% 5.26/2.01  Abstraction          : 0.05
% 5.26/2.01  MUC search           : 0.00
% 5.26/2.01  Cooper               : 0.00
% 5.26/2.01  Total                : 1.27
% 5.26/2.01  Index Insertion      : 0.00
% 5.26/2.01  Index Deletion       : 0.00
% 5.26/2.01  Index Matching       : 0.00
% 5.26/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
