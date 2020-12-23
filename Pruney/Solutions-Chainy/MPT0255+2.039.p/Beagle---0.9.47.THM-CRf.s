%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:44 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 158 expanded)
%              Number of leaves         :   26 (  65 expanded)
%              Depth                    :   10
%              Number of atoms          :   45 ( 178 expanded)
%              Number of equality atoms :   18 (  98 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_57,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_214,plain,(
    ! [A_49] : k2_xboole_0(k1_xboole_0,A_49) = A_49 ),
    inference(resolution,[status(thm)],[c_18,c_160])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_227,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_48,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_56,plain,(
    ! [B_38,A_39] : k2_xboole_0(B_38,A_39) = k2_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_14,B_15] : r1_tarski(A_14,k2_xboole_0(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_71,plain,(
    ! [A_39,B_38] : r1_tarski(A_39,k2_xboole_0(B_38,A_39)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_22])).

tff(c_108,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_71])).

tff(c_180,plain,(
    k2_xboole_0('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_108,c_160])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_180])).

tff(c_230,plain,(
    ! [A_49] : k2_xboole_0(A_49,k1_xboole_0) = A_49 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_2])).

tff(c_346,plain,(
    ! [A_49] : k2_xboole_0(A_49,'#skF_6') = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_230])).

tff(c_316,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_48])).

tff(c_408,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_346,c_316])).

tff(c_28,plain,(
    ! [D_21,B_17] : r2_hidden(D_21,k2_tarski(D_21,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_487,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_28])).

tff(c_20,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_318,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_20])).

tff(c_542,plain,(
    ! [A_62,B_63,C_64] :
      ( ~ r1_xboole_0(A_62,B_63)
      | ~ r2_hidden(C_64,B_63)
      | ~ r2_hidden(C_64,A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_547,plain,(
    ! [C_65,A_66] :
      ( ~ r2_hidden(C_65,'#skF_6')
      | ~ r2_hidden(C_65,A_66) ) ),
    inference(resolution,[status(thm)],[c_318,c_542])).

tff(c_559,plain,(
    ! [A_66] : ~ r2_hidden('#skF_4',A_66) ),
    inference(resolution,[status(thm)],[c_487,c_547])).

tff(c_564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_559,c_487])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:08:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  
% 2.22/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.22/1.38  
% 2.22/1.38  %Foreground sorts:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Background operators:
% 2.22/1.38  
% 2.22/1.38  
% 2.22/1.38  %Foreground operators:
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.22/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.22/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.38  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.22/1.38  
% 2.22/1.39  tff(f_57, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.22/1.39  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.22/1.39  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.22/1.39  tff(f_80, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.22/1.39  tff(f_61, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.22/1.39  tff(f_70, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.22/1.39  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.22/1.39  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.22/1.39  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.22/1.39  tff(c_160, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.39  tff(c_214, plain, (![A_49]: (k2_xboole_0(k1_xboole_0, A_49)=A_49)), inference(resolution, [status(thm)], [c_18, c_160])).
% 2.22/1.39  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.39  tff(c_227, plain, (![A_49]: (k2_xboole_0(A_49, k1_xboole_0)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_214, c_2])).
% 2.22/1.39  tff(c_48, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.22/1.39  tff(c_56, plain, (![B_38, A_39]: (k2_xboole_0(B_38, A_39)=k2_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.39  tff(c_22, plain, (![A_14, B_15]: (r1_tarski(A_14, k2_xboole_0(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.39  tff(c_71, plain, (![A_39, B_38]: (r1_tarski(A_39, k2_xboole_0(B_38, A_39)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_22])).
% 2.22/1.39  tff(c_108, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_71])).
% 2.22/1.39  tff(c_180, plain, (k2_xboole_0('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_108, c_160])).
% 2.22/1.39  tff(c_255, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_180])).
% 2.22/1.39  tff(c_230, plain, (![A_49]: (k2_xboole_0(A_49, k1_xboole_0)=A_49)), inference(superposition, [status(thm), theory('equality')], [c_214, c_2])).
% 2.22/1.39  tff(c_346, plain, (![A_49]: (k2_xboole_0(A_49, '#skF_6')=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_255, c_230])).
% 2.22/1.39  tff(c_316, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_255, c_48])).
% 2.22/1.39  tff(c_408, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_346, c_316])).
% 2.22/1.39  tff(c_28, plain, (![D_21, B_17]: (r2_hidden(D_21, k2_tarski(D_21, B_17)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.22/1.39  tff(c_487, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_408, c_28])).
% 2.22/1.39  tff(c_20, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.22/1.39  tff(c_318, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_20])).
% 2.22/1.39  tff(c_542, plain, (![A_62, B_63, C_64]: (~r1_xboole_0(A_62, B_63) | ~r2_hidden(C_64, B_63) | ~r2_hidden(C_64, A_62))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.22/1.39  tff(c_547, plain, (![C_65, A_66]: (~r2_hidden(C_65, '#skF_6') | ~r2_hidden(C_65, A_66))), inference(resolution, [status(thm)], [c_318, c_542])).
% 2.22/1.39  tff(c_559, plain, (![A_66]: (~r2_hidden('#skF_4', A_66))), inference(resolution, [status(thm)], [c_487, c_547])).
% 2.22/1.39  tff(c_564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_559, c_487])).
% 2.22/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.39  
% 2.22/1.39  Inference rules
% 2.22/1.39  ----------------------
% 2.22/1.39  #Ref     : 0
% 2.22/1.39  #Sup     : 123
% 2.22/1.39  #Fact    : 0
% 2.22/1.39  #Define  : 0
% 2.22/1.39  #Split   : 0
% 2.22/1.39  #Chain   : 0
% 2.22/1.39  #Close   : 0
% 2.22/1.39  
% 2.22/1.39  Ordering : KBO
% 2.22/1.39  
% 2.22/1.39  Simplification rules
% 2.22/1.39  ----------------------
% 2.22/1.39  #Subsume      : 0
% 2.22/1.39  #Demod        : 75
% 2.22/1.39  #Tautology    : 101
% 2.22/1.39  #SimpNegUnit  : 1
% 2.22/1.39  #BackRed      : 11
% 2.22/1.39  
% 2.22/1.39  #Partial instantiations: 0
% 2.22/1.39  #Strategies tried      : 1
% 2.22/1.39  
% 2.22/1.39  Timing (in seconds)
% 2.22/1.39  ----------------------
% 2.22/1.39  Preprocessing        : 0.33
% 2.22/1.39  Parsing              : 0.17
% 2.22/1.39  CNF conversion       : 0.02
% 2.22/1.39  Main loop            : 0.24
% 2.22/1.39  Inferencing          : 0.08
% 2.22/1.39  Reduction            : 0.09
% 2.22/1.39  Demodulation         : 0.07
% 2.22/1.39  BG Simplification    : 0.01
% 2.22/1.39  Subsumption          : 0.04
% 2.22/1.39  Abstraction          : 0.02
% 2.22/1.39  MUC search           : 0.00
% 2.22/1.39  Cooper               : 0.00
% 2.22/1.40  Total                : 0.60
% 2.22/1.40  Index Insertion      : 0.00
% 2.22/1.40  Index Deletion       : 0.00
% 2.22/1.40  Index Matching       : 0.00
% 2.22/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
