%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   48 (  84 expanded)
%              Number of leaves         :   25 (  39 expanded)
%              Depth                    :    9
%              Number of atoms          :   39 (  79 expanded)
%              Number of equality atoms :   21 (  51 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_80,plain,(
    ! [B_33,A_34] : k2_xboole_0(B_33,A_34) = k2_xboole_0(A_34,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_130,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_243,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_249,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_243,c_4])).

tff(c_251,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_249])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_259,plain,(
    ! [A_6] : r1_xboole_0(A_6,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_8])).

tff(c_308,plain,(
    ! [A_43,B_44] :
      ( ~ r2_hidden(A_43,B_44)
      | ~ r1_xboole_0(k1_tarski(A_43),B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_313,plain,(
    ! [A_43] : ~ r2_hidden(A_43,'#skF_4') ),
    inference(resolution,[status(thm)],[c_259,c_308])).

tff(c_127,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_80])).

tff(c_370,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_127])).

tff(c_108,plain,(
    ! [A_34] : k2_xboole_0(k1_xboole_0,A_34) = A_34 ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_255,plain,(
    ! [A_34] : k2_xboole_0('#skF_4',A_34) = A_34 ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_108])).

tff(c_374,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_255])).

tff(c_30,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [D_25,B_26] : r2_hidden(D_25,k2_tarski(D_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_65,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_62])).

tff(c_395,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_65])).

tff(c_399,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_313,c_395])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:39:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.21  
% 2.06/1.22  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.06/1.22  tff(f_61, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.22  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.22  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.22  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.06/1.22  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.06/1.22  tff(f_55, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.06/1.22  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.22  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.22  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.22  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.22  tff(c_80, plain, (![B_33, A_34]: (k2_xboole_0(B_33, A_34)=k2_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.22  tff(c_130, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_80])).
% 2.06/1.22  tff(c_10, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.22  tff(c_243, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_130, c_10])).
% 2.06/1.23  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.23  tff(c_249, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_243, c_4])).
% 2.06/1.23  tff(c_251, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_249])).
% 2.06/1.23  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.23  tff(c_259, plain, (![A_6]: (r1_xboole_0(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_8])).
% 2.06/1.23  tff(c_308, plain, (![A_43, B_44]: (~r2_hidden(A_43, B_44) | ~r1_xboole_0(k1_tarski(A_43), B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.06/1.23  tff(c_313, plain, (![A_43]: (~r2_hidden(A_43, '#skF_4'))), inference(resolution, [status(thm)], [c_259, c_308])).
% 2.06/1.23  tff(c_127, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_80])).
% 2.06/1.23  tff(c_370, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_251, c_127])).
% 2.06/1.23  tff(c_108, plain, (![A_34]: (k2_xboole_0(k1_xboole_0, A_34)=A_34)), inference(superposition, [status(thm), theory('equality')], [c_80, c_6])).
% 2.06/1.23  tff(c_255, plain, (![A_34]: (k2_xboole_0('#skF_4', A_34)=A_34)), inference(demodulation, [status(thm), theory('equality')], [c_251, c_108])).
% 2.06/1.23  tff(c_374, plain, (k1_tarski('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_370, c_255])).
% 2.06/1.23  tff(c_30, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.06/1.23  tff(c_62, plain, (![D_25, B_26]: (r2_hidden(D_25, k2_tarski(D_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.23  tff(c_65, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_62])).
% 2.06/1.23  tff(c_395, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_374, c_65])).
% 2.06/1.23  tff(c_399, plain, $false, inference(negUnitSimplification, [status(thm)], [c_313, c_395])).
% 2.06/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  Inference rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Ref     : 0
% 2.06/1.23  #Sup     : 86
% 2.06/1.23  #Fact    : 0
% 2.06/1.23  #Define  : 0
% 2.06/1.23  #Split   : 0
% 2.06/1.23  #Chain   : 0
% 2.06/1.23  #Close   : 0
% 2.06/1.23  
% 2.06/1.23  Ordering : KBO
% 2.06/1.23  
% 2.06/1.23  Simplification rules
% 2.06/1.23  ----------------------
% 2.06/1.23  #Subsume      : 0
% 2.06/1.23  #Demod        : 32
% 2.06/1.23  #Tautology    : 61
% 2.06/1.23  #SimpNegUnit  : 1
% 2.06/1.23  #BackRed      : 10
% 2.06/1.23  
% 2.06/1.23  #Partial instantiations: 0
% 2.06/1.23  #Strategies tried      : 1
% 2.06/1.23  
% 2.06/1.23  Timing (in seconds)
% 2.06/1.23  ----------------------
% 2.08/1.23  Preprocessing        : 0.29
% 2.08/1.23  Parsing              : 0.15
% 2.08/1.23  CNF conversion       : 0.02
% 2.08/1.23  Main loop            : 0.18
% 2.08/1.23  Inferencing          : 0.06
% 2.08/1.23  Reduction            : 0.07
% 2.08/1.23  Demodulation         : 0.05
% 2.08/1.23  BG Simplification    : 0.01
% 2.08/1.23  Subsumption          : 0.03
% 2.08/1.23  Abstraction          : 0.01
% 2.08/1.23  MUC search           : 0.00
% 2.08/1.23  Cooper               : 0.00
% 2.08/1.23  Total                : 0.50
% 2.08/1.23  Index Insertion      : 0.00
% 2.08/1.23  Index Deletion       : 0.00
% 2.08/1.23  Index Matching       : 0.00
% 2.08/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
