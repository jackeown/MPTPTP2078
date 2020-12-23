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
% DateTime   : Thu Dec  3 09:45:10 EST 2020

% Result     : Theorem 2.78s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   47 (  55 expanded)
%              Number of leaves         :   22 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   41 (  53 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_46,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_42,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r2_xboole_0(A,B)
          & k4_xboole_0(B,A) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_6,plain,(
    ! [B_4] : ~ r2_xboole_0(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [A_9] : k3_xboole_0(A_9,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_30,plain,(
    r2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_121,plain,(
    ! [A_29,B_30] :
      ( r1_tarski(A_29,B_30)
      | ~ r2_xboole_0(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_125,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_121])).

tff(c_176,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_180,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_125,c_176])).

tff(c_28,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_200,plain,(
    ! [A_36,B_37] : k2_xboole_0(A_36,k4_xboole_0(B_37,A_36)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_209,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_200])).

tff(c_212,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_209])).

tff(c_278,plain,(
    ! [A_44,B_45] : k5_xboole_0(k5_xboole_0(A_44,B_45),k2_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_302,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1',k1_xboole_0),'#skF_2') = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_278])).

tff(c_332,plain,(
    k5_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14,c_302])).

tff(c_74,plain,(
    ! [B_27,A_28] : k5_xboole_0(B_27,A_28) = k5_xboole_0(A_28,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_74])).

tff(c_24,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_428,plain,(
    ! [A_48,B_49,C_50] : k5_xboole_0(k5_xboole_0(A_48,B_49),C_50) = k5_xboole_0(A_48,k5_xboole_0(B_49,C_50)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_519,plain,(
    ! [A_18,C_50] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_50)) = k5_xboole_0(k1_xboole_0,C_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_428])).

tff(c_535,plain,(
    ! [A_51,C_52] : k5_xboole_0(A_51,k5_xboole_0(A_51,C_52)) = C_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_519])).

tff(c_574,plain,(
    k5_xboole_0('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_535])).

tff(c_609,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_574])).

tff(c_623,plain,(
    r2_xboole_0('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_30])).

tff(c_626,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_623])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:56:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.78/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.76  
% 2.78/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.77  %$ r2_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 2.78/1.77  
% 2.78/1.77  %Foreground sorts:
% 2.78/1.77  
% 2.78/1.77  
% 2.78/1.77  %Background operators:
% 2.78/1.77  
% 2.78/1.77  
% 2.78/1.77  %Foreground operators:
% 2.78/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.77  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.77  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.77  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.77  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.78/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.78/1.77  
% 3.04/1.78  tff(f_34, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 3.04/1.78  tff(f_46, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.04/1.78  tff(f_42, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.04/1.78  tff(f_63, negated_conjecture, ~(![A, B]: ~(r2_xboole_0(A, B) & (k4_xboole_0(B, A) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t105_xboole_1)).
% 3.04/1.78  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.04/1.78  tff(f_44, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 3.04/1.78  tff(f_57, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.04/1.78  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.04/1.78  tff(f_55, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.04/1.78  tff(f_53, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.04/1.78  tff(c_6, plain, (![B_4]: (~r2_xboole_0(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.78  tff(c_18, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.04/1.78  tff(c_14, plain, (![A_9]: (k3_xboole_0(A_9, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.04/1.78  tff(c_30, plain, (r2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.78  tff(c_121, plain, (![A_29, B_30]: (r1_tarski(A_29, B_30) | ~r2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.04/1.78  tff(c_125, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_121])).
% 3.04/1.78  tff(c_176, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.04/1.78  tff(c_180, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_125, c_176])).
% 3.04/1.78  tff(c_28, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.04/1.78  tff(c_200, plain, (![A_36, B_37]: (k2_xboole_0(A_36, k4_xboole_0(B_37, A_36))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.04/1.78  tff(c_209, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28, c_200])).
% 3.04/1.78  tff(c_212, plain, (k2_xboole_0('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_209])).
% 3.04/1.78  tff(c_278, plain, (![A_44, B_45]: (k5_xboole_0(k5_xboole_0(A_44, B_45), k2_xboole_0(A_44, B_45))=k3_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.04/1.78  tff(c_302, plain, (k5_xboole_0(k5_xboole_0('#skF_1', k1_xboole_0), '#skF_2')=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_212, c_278])).
% 3.04/1.78  tff(c_332, plain, (k5_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14, c_302])).
% 3.04/1.78  tff(c_74, plain, (![B_27, A_28]: (k5_xboole_0(B_27, A_28)=k5_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.04/1.78  tff(c_112, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(superposition, [status(thm), theory('equality')], [c_18, c_74])).
% 3.04/1.78  tff(c_24, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.04/1.78  tff(c_428, plain, (![A_48, B_49, C_50]: (k5_xboole_0(k5_xboole_0(A_48, B_49), C_50)=k5_xboole_0(A_48, k5_xboole_0(B_49, C_50)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.04/1.78  tff(c_519, plain, (![A_18, C_50]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_50))=k5_xboole_0(k1_xboole_0, C_50))), inference(superposition, [status(thm), theory('equality')], [c_24, c_428])).
% 3.04/1.78  tff(c_535, plain, (![A_51, C_52]: (k5_xboole_0(A_51, k5_xboole_0(A_51, C_52))=C_52)), inference(demodulation, [status(thm), theory('equality')], [c_112, c_519])).
% 3.04/1.78  tff(c_574, plain, (k5_xboole_0('#skF_1', k1_xboole_0)='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_332, c_535])).
% 3.04/1.78  tff(c_609, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_574])).
% 3.04/1.78  tff(c_623, plain, (r2_xboole_0('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_609, c_30])).
% 3.04/1.78  tff(c_626, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_623])).
% 3.04/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.78  
% 3.04/1.78  Inference rules
% 3.04/1.78  ----------------------
% 3.04/1.78  #Ref     : 0
% 3.04/1.78  #Sup     : 152
% 3.04/1.78  #Fact    : 0
% 3.04/1.78  #Define  : 0
% 3.04/1.79  #Split   : 0
% 3.04/1.79  #Chain   : 0
% 3.04/1.79  #Close   : 0
% 3.04/1.79  
% 3.04/1.79  Ordering : KBO
% 3.04/1.79  
% 3.04/1.79  Simplification rules
% 3.04/1.79  ----------------------
% 3.04/1.79  #Subsume      : 1
% 3.04/1.79  #Demod        : 72
% 3.04/1.79  #Tautology    : 91
% 3.04/1.79  #SimpNegUnit  : 1
% 3.04/1.79  #BackRed      : 10
% 3.04/1.79  
% 3.04/1.79  #Partial instantiations: 0
% 3.04/1.79  #Strategies tried      : 1
% 3.04/1.79  
% 3.04/1.79  Timing (in seconds)
% 3.04/1.79  ----------------------
% 3.04/1.79  Preprocessing        : 0.46
% 3.04/1.79  Parsing              : 0.26
% 3.04/1.79  CNF conversion       : 0.03
% 3.04/1.79  Main loop            : 0.46
% 3.04/1.79  Inferencing          : 0.15
% 3.07/1.79  Reduction            : 0.18
% 3.07/1.79  Demodulation         : 0.15
% 3.07/1.79  BG Simplification    : 0.02
% 3.07/1.79  Subsumption          : 0.07
% 3.07/1.79  Abstraction          : 0.02
% 3.07/1.79  MUC search           : 0.00
% 3.07/1.79  Cooper               : 0.00
% 3.07/1.79  Total                : 0.96
% 3.07/1.79  Index Insertion      : 0.00
% 3.07/1.79  Index Deletion       : 0.00
% 3.07/1.79  Index Matching       : 0.00
% 3.07/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
