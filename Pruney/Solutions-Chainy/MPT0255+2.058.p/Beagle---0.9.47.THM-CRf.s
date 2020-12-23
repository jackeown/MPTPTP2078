%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:46 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   51 ( 105 expanded)
%              Number of leaves         :   29 (  50 expanded)
%              Depth                    :   11
%              Number of atoms          :   42 (  98 expanded)
%              Number of equality atoms :   15 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_47,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_41,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    k2_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_94,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k2_xboole_0(A_39,B_40)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_126,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k2_xboole_0(B_42,A_41)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_94])).

tff(c_136,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_126])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_136])).

tff(c_14,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_170,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_14])).

tff(c_324,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_2'(A_53,B_54),A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_328,plain,(
    ! [A_53,B_54] :
      ( ~ v1_xboole_0(A_53)
      | r1_tarski(A_53,B_54) ) ),
    inference(resolution,[status(thm)],[c_324,c_4])).

tff(c_168,plain,(
    ! [A_15] : k4_xboole_0(A_15,'#skF_5') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_20])).

tff(c_22,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k2_xboole_0(A_16,B_17)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    k4_xboole_0(k2_tarski('#skF_3','#skF_4'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_208,plain,(
    k2_tarski('#skF_3','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_149,c_149,c_110])).

tff(c_332,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r1_tarski(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_341,plain,(
    ! [C_60] :
      ( r2_hidden('#skF_3',C_60)
      | ~ r1_tarski('#skF_5',C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_332])).

tff(c_346,plain,(
    ! [C_61] :
      ( ~ v1_xboole_0(C_61)
      | ~ r1_tarski('#skF_5',C_61) ) ),
    inference(resolution,[status(thm)],[c_341,c_4])).

tff(c_350,plain,(
    ! [B_54] :
      ( ~ v1_xboole_0(B_54)
      | ~ v1_xboole_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_328,c_346])).

tff(c_353,plain,(
    ! [B_54] : ~ v1_xboole_0(B_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_170,c_350])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n018.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:44:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  
% 2.02/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.29  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2
% 2.02/1.29  
% 2.02/1.29  %Foreground sorts:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Background operators:
% 2.02/1.29  
% 2.02/1.29  
% 2.02/1.29  %Foreground operators:
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.02/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.02/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.02/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.02/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.02/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.02/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.29  
% 2.02/1.30  tff(f_47, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.02/1.30  tff(f_67, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.02/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.02/1.30  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.02/1.30  tff(f_41, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.02/1.30  tff(f_40, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.02/1.30  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.02/1.30  tff(f_63, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.02/1.30  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.02/1.30  tff(c_38, plain, (k2_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.02/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.02/1.30  tff(c_94, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k2_xboole_0(A_39, B_40))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.30  tff(c_126, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k2_xboole_0(B_42, A_41))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_94])).
% 2.02/1.30  tff(c_136, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_126])).
% 2.02/1.30  tff(c_149, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_136])).
% 2.02/1.30  tff(c_14, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.02/1.30  tff(c_170, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_149, c_14])).
% 2.02/1.30  tff(c_324, plain, (![A_53, B_54]: (r2_hidden('#skF_2'(A_53, B_54), A_53) | r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.02/1.30  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.02/1.30  tff(c_328, plain, (![A_53, B_54]: (~v1_xboole_0(A_53) | r1_tarski(A_53, B_54))), inference(resolution, [status(thm)], [c_324, c_4])).
% 2.02/1.30  tff(c_168, plain, (![A_15]: (k4_xboole_0(A_15, '#skF_5')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_149, c_20])).
% 2.02/1.30  tff(c_22, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k2_xboole_0(A_16, B_17))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.02/1.30  tff(c_110, plain, (k4_xboole_0(k2_tarski('#skF_3', '#skF_4'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_22])).
% 2.02/1.30  tff(c_208, plain, (k2_tarski('#skF_3', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_149, c_149, c_110])).
% 2.02/1.30  tff(c_332, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r1_tarski(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.02/1.30  tff(c_341, plain, (![C_60]: (r2_hidden('#skF_3', C_60) | ~r1_tarski('#skF_5', C_60))), inference(superposition, [status(thm), theory('equality')], [c_208, c_332])).
% 2.02/1.30  tff(c_346, plain, (![C_61]: (~v1_xboole_0(C_61) | ~r1_tarski('#skF_5', C_61))), inference(resolution, [status(thm)], [c_341, c_4])).
% 2.02/1.30  tff(c_350, plain, (![B_54]: (~v1_xboole_0(B_54) | ~v1_xboole_0('#skF_5'))), inference(resolution, [status(thm)], [c_328, c_346])).
% 2.02/1.30  tff(c_353, plain, (![B_54]: (~v1_xboole_0(B_54))), inference(demodulation, [status(thm), theory('equality')], [c_170, c_350])).
% 2.02/1.30  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_353, c_170])).
% 2.02/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.30  
% 2.02/1.30  Inference rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Ref     : 0
% 2.02/1.30  #Sup     : 85
% 2.02/1.30  #Fact    : 0
% 2.02/1.30  #Define  : 0
% 2.02/1.30  #Split   : 0
% 2.02/1.30  #Chain   : 0
% 2.02/1.30  #Close   : 0
% 2.02/1.30  
% 2.02/1.30  Ordering : KBO
% 2.02/1.30  
% 2.02/1.30  Simplification rules
% 2.02/1.30  ----------------------
% 2.02/1.30  #Subsume      : 3
% 2.02/1.30  #Demod        : 44
% 2.02/1.30  #Tautology    : 73
% 2.02/1.30  #SimpNegUnit  : 2
% 2.02/1.30  #BackRed      : 10
% 2.02/1.30  
% 2.02/1.30  #Partial instantiations: 0
% 2.02/1.30  #Strategies tried      : 1
% 2.02/1.30  
% 2.02/1.30  Timing (in seconds)
% 2.02/1.30  ----------------------
% 2.02/1.30  Preprocessing        : 0.34
% 2.02/1.30  Parsing              : 0.18
% 2.02/1.30  CNF conversion       : 0.02
% 2.02/1.30  Main loop            : 0.19
% 2.02/1.30  Inferencing          : 0.07
% 2.02/1.30  Reduction            : 0.07
% 2.02/1.30  Demodulation         : 0.06
% 2.02/1.30  BG Simplification    : 0.01
% 2.02/1.30  Subsumption          : 0.03
% 2.02/1.30  Abstraction          : 0.01
% 2.02/1.30  MUC search           : 0.00
% 2.02/1.30  Cooper               : 0.00
% 2.02/1.30  Total                : 0.57
% 2.02/1.30  Index Insertion      : 0.00
% 2.02/1.30  Index Deletion       : 0.00
% 2.02/1.30  Index Matching       : 0.00
% 2.02/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
