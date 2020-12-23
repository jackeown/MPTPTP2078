%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:46 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   47 (  53 expanded)
%              Number of leaves         :   26 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   37 (  49 expanded)
%              Number of equality atoms :   29 (  41 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_32,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_182,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,k1_tarski(B_51)) = A_50
      | r2_hidden(B_51,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_188,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_36])).

tff(c_196,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_188])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_45,A_46] : k5_xboole_0(B_45,A_46) = k5_xboole_0(A_46,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_46] : k5_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_6])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_300,plain,(
    ! [A_65,B_66,C_67] : k5_xboole_0(k5_xboole_0(A_65,B_66),C_67) = k5_xboole_0(A_65,k5_xboole_0(B_66,C_67)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_357,plain,(
    ! [A_9,C_67] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_67)) = k5_xboole_0(k1_xboole_0,C_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_300])).

tff(c_378,plain,(
    ! [A_68,C_69] : k5_xboole_0(A_68,k5_xboole_0(A_68,C_69)) = C_69 ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_357])).

tff(c_766,plain,(
    ! [A_91,B_92] : k5_xboole_0(A_91,k4_xboole_0(A_91,B_92)) = k3_xboole_0(A_91,B_92) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_378])).

tff(c_812,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k5_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_766])).

tff(c_820,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_812])).

tff(c_26,plain,(
    ! [B_39,A_38] :
      ( k3_xboole_0(B_39,k1_tarski(A_38)) = k1_tarski(A_38)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_824,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_820,c_26])).

tff(c_834,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_824])).

tff(c_836,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:47:36 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.50/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.35  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.50/1.35  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.50/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.35  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.35  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.50/1.35  
% 2.50/1.36  tff(f_68, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 2.50/1.36  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.50/1.36  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.50/1.36  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.50/1.36  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.50/1.36  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.50/1.36  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 2.50/1.36  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 2.50/1.36  tff(c_32, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.36  tff(c_34, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.36  tff(c_182, plain, (![A_50, B_51]: (k4_xboole_0(A_50, k1_tarski(B_51))=A_50 | r2_hidden(B_51, A_50))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.50/1.36  tff(c_36, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.50/1.36  tff(c_188, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_182, c_36])).
% 2.50/1.36  tff(c_196, plain, (r2_hidden('#skF_2', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_34, c_188])).
% 2.50/1.36  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.36  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.50/1.36  tff(c_76, plain, (![B_45, A_46]: (k5_xboole_0(B_45, A_46)=k5_xboole_0(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.36  tff(c_92, plain, (![A_46]: (k5_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_76, c_6])).
% 2.50/1.36  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.36  tff(c_300, plain, (![A_65, B_66, C_67]: (k5_xboole_0(k5_xboole_0(A_65, B_66), C_67)=k5_xboole_0(A_65, k5_xboole_0(B_66, C_67)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.50/1.36  tff(c_357, plain, (![A_9, C_67]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_67))=k5_xboole_0(k1_xboole_0, C_67))), inference(superposition, [status(thm), theory('equality')], [c_10, c_300])).
% 2.50/1.36  tff(c_378, plain, (![A_68, C_69]: (k5_xboole_0(A_68, k5_xboole_0(A_68, C_69))=C_69)), inference(demodulation, [status(thm), theory('equality')], [c_92, c_357])).
% 2.50/1.36  tff(c_766, plain, (![A_91, B_92]: (k5_xboole_0(A_91, k4_xboole_0(A_91, B_92))=k3_xboole_0(A_91, B_92))), inference(superposition, [status(thm), theory('equality')], [c_4, c_378])).
% 2.50/1.36  tff(c_812, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k5_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_36, c_766])).
% 2.50/1.36  tff(c_820, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_812])).
% 2.50/1.36  tff(c_26, plain, (![B_39, A_38]: (k3_xboole_0(B_39, k1_tarski(A_38))=k1_tarski(A_38) | ~r2_hidden(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.50/1.36  tff(c_824, plain, (k1_tarski('#skF_2')='#skF_1' | ~r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_820, c_26])).
% 2.50/1.36  tff(c_834, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_824])).
% 2.50/1.36  tff(c_836, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_834])).
% 2.50/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  Inference rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Ref     : 0
% 2.50/1.36  #Sup     : 194
% 2.50/1.36  #Fact    : 0
% 2.50/1.36  #Define  : 0
% 2.50/1.36  #Split   : 0
% 2.50/1.36  #Chain   : 0
% 2.50/1.36  #Close   : 0
% 2.50/1.36  
% 2.50/1.36  Ordering : KBO
% 2.50/1.36  
% 2.50/1.36  Simplification rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Subsume      : 7
% 2.50/1.36  #Demod        : 88
% 2.50/1.36  #Tautology    : 140
% 2.50/1.36  #SimpNegUnit  : 3
% 2.50/1.36  #BackRed      : 0
% 2.50/1.36  
% 2.50/1.36  #Partial instantiations: 0
% 2.50/1.36  #Strategies tried      : 1
% 2.50/1.36  
% 2.50/1.36  Timing (in seconds)
% 2.50/1.36  ----------------------
% 2.50/1.37  Preprocessing        : 0.31
% 2.50/1.37  Parsing              : 0.17
% 2.50/1.37  CNF conversion       : 0.02
% 2.50/1.37  Main loop            : 0.29
% 2.50/1.37  Inferencing          : 0.11
% 2.50/1.37  Reduction            : 0.11
% 2.50/1.37  Demodulation         : 0.09
% 2.50/1.37  BG Simplification    : 0.02
% 2.50/1.37  Subsumption          : 0.03
% 2.50/1.37  Abstraction          : 0.02
% 2.50/1.37  MUC search           : 0.00
% 2.50/1.37  Cooper               : 0.00
% 2.50/1.37  Total                : 0.62
% 2.50/1.37  Index Insertion      : 0.00
% 2.50/1.37  Index Deletion       : 0.00
% 2.50/1.37  Index Matching       : 0.00
% 2.50/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
