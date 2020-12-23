%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:52 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   43 (  45 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  47 expanded)
%              Number of equality atoms :   40 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_29,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_24,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_26,B_27] : k4_xboole_0(k1_tarski(A_26),k2_tarski(A_26,B_27)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_75,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_16,plain,(
    ! [B_14] : k4_xboole_0(k1_tarski(B_14),k1_tarski(B_14)) != k1_tarski(B_14) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_100,plain,(
    ! [B_14] : k1_tarski(B_14) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_16])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_6,plain,(
    ! [A_4] : k4_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_78,plain,(
    ! [A_28,B_29] : k5_xboole_0(A_28,k3_xboole_0(A_28,B_29)) = k4_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_87,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = k4_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_78])).

tff(c_90,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_28,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_109,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k4_xboole_0(B_34,A_33)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_124,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_109])).

tff(c_132,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_124])).

tff(c_247,plain,(
    ! [C_45,B_46,A_47] :
      ( k1_xboole_0 = C_45
      | k1_xboole_0 = B_46
      | C_45 = B_46
      | k2_xboole_0(B_46,C_45) != k1_tarski(A_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_262,plain,(
    ! [A_47] :
      ( k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = k1_xboole_0
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_47) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_247])).

tff(c_267,plain,(
    ! [A_47] : k1_tarski(A_47) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_100,c_26,c_262])).

tff(c_280,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_267])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:30:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  
% 1.93/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.20  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.93/1.20  
% 1.93/1.20  %Foreground sorts:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Background operators:
% 1.93/1.20  
% 1.93/1.20  
% 1.93/1.20  %Foreground operators:
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.93/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.93/1.20  
% 1.93/1.21  tff(f_68, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.93/1.21  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.21  tff(f_46, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.93/1.21  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.93/1.21  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.93/1.21  tff(f_29, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.93/1.21  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.93/1.21  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.93/1.21  tff(f_58, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.93/1.21  tff(c_24, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.21  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.93/1.21  tff(c_68, plain, (![A_26, B_27]: (k4_xboole_0(k1_tarski(A_26), k2_tarski(A_26, B_27))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.93/1.21  tff(c_75, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 1.93/1.21  tff(c_16, plain, (![B_14]: (k4_xboole_0(k1_tarski(B_14), k1_tarski(B_14))!=k1_tarski(B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.93/1.21  tff(c_100, plain, (![B_14]: (k1_tarski(B_14)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_16])).
% 1.93/1.21  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.21  tff(c_6, plain, (![A_4]: (k4_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.93/1.21  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.93/1.21  tff(c_78, plain, (![A_28, B_29]: (k5_xboole_0(A_28, k3_xboole_0(A_28, B_29))=k4_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.93/1.21  tff(c_87, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=k4_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_78])).
% 1.93/1.21  tff(c_90, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_87])).
% 1.93/1.21  tff(c_28, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.21  tff(c_109, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k4_xboole_0(B_34, A_33))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.93/1.21  tff(c_124, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_109])).
% 1.93/1.21  tff(c_132, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_124])).
% 1.93/1.21  tff(c_247, plain, (![C_45, B_46, A_47]: (k1_xboole_0=C_45 | k1_xboole_0=B_46 | C_45=B_46 | k2_xboole_0(B_46, C_45)!=k1_tarski(A_47))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.21  tff(c_262, plain, (![A_47]: (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_47)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_132, c_247])).
% 1.93/1.21  tff(c_267, plain, (![A_47]: (k1_tarski(A_47)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_100, c_26, c_262])).
% 1.93/1.21  tff(c_280, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_267])).
% 1.93/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  Inference rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Ref     : 1
% 1.93/1.21  #Sup     : 60
% 1.93/1.21  #Fact    : 0
% 1.93/1.21  #Define  : 0
% 1.93/1.21  #Split   : 0
% 1.93/1.21  #Chain   : 0
% 1.93/1.21  #Close   : 0
% 1.93/1.21  
% 1.93/1.21  Ordering : KBO
% 1.93/1.21  
% 1.93/1.21  Simplification rules
% 1.93/1.21  ----------------------
% 1.93/1.21  #Subsume      : 1
% 1.93/1.21  #Demod        : 13
% 1.93/1.21  #Tautology    : 48
% 1.93/1.21  #SimpNegUnit  : 5
% 1.93/1.21  #BackRed      : 1
% 1.93/1.21  
% 1.93/1.21  #Partial instantiations: 0
% 1.93/1.21  #Strategies tried      : 1
% 1.93/1.21  
% 1.93/1.21  Timing (in seconds)
% 1.93/1.21  ----------------------
% 1.93/1.21  Preprocessing        : 0.28
% 1.93/1.21  Parsing              : 0.14
% 1.93/1.21  CNF conversion       : 0.02
% 1.93/1.21  Main loop            : 0.16
% 1.93/1.21  Inferencing          : 0.06
% 1.93/1.21  Reduction            : 0.05
% 1.93/1.21  Demodulation         : 0.04
% 1.93/1.21  BG Simplification    : 0.01
% 1.93/1.21  Subsumption          : 0.02
% 1.93/1.21  Abstraction          : 0.01
% 1.93/1.21  MUC search           : 0.00
% 1.93/1.21  Cooper               : 0.00
% 1.93/1.21  Total                : 0.46
% 1.93/1.21  Index Insertion      : 0.00
% 1.93/1.21  Index Deletion       : 0.00
% 1.93/1.21  Index Matching       : 0.00
% 1.93/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
