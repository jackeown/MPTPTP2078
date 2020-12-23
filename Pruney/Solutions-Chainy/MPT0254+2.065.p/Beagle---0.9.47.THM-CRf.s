%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:28 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   46 (  73 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   36 (  67 expanded)
%              Number of equality atoms :   17 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
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

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_111,plain,(
    ! [B_36,A_37] : k2_xboole_0(B_36,A_37) = k2_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_55,plain,(
    ! [A_26,B_27] : r1_tarski(A_26,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_55])).

tff(c_6,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_6])).

tff(c_75,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_40])).

tff(c_126,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_75])).

tff(c_172,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_8,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_194,plain,(
    ! [A_5] : r1_xboole_0(A_5,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_261,plain,(
    ! [A_45,B_46] :
      ( ~ r2_hidden(A_45,B_46)
      | ~ r1_xboole_0(k1_tarski(A_45),B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    ! [A_45] : ~ r2_hidden(A_45,'#skF_4') ),
    inference(resolution,[status(thm)],[c_194,c_261])).

tff(c_90,plain,(
    ! [A_32] : k2_tarski(A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [D_13,A_8] : r2_hidden(D_13,k2_tarski(A_8,D_13)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_102,plain,(
    ! [A_33] : r2_hidden(A_33,k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_14])).

tff(c_105,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_102])).

tff(c_189,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_105])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n022.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 09:30:10 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.35  
% 2.09/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.09/1.35  
% 2.09/1.35  %Foreground sorts:
% 2.09/1.35  
% 2.09/1.35  
% 2.09/1.35  %Background operators:
% 2.09/1.35  
% 2.09/1.35  
% 2.09/1.35  %Foreground operators:
% 2.09/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.35  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.09/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.35  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.09/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.35  
% 2.19/1.36  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.19/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.19/1.36  tff(f_63, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.19/1.36  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.19/1.36  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.19/1.36  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.19/1.36  tff(f_57, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.19/1.36  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.36  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.19/1.36  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.19/1.36  tff(c_111, plain, (![B_36, A_37]: (k2_xboole_0(B_36, A_37)=k2_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.36  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.19/1.36  tff(c_55, plain, (![A_26, B_27]: (r1_tarski(A_26, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.36  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_55])).
% 2.19/1.36  tff(c_6, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.36  tff(c_73, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_6])).
% 2.19/1.36  tff(c_75, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_73, c_40])).
% 2.19/1.36  tff(c_126, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_111, c_75])).
% 2.19/1.36  tff(c_172, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_126])).
% 2.19/1.36  tff(c_8, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.36  tff(c_194, plain, (![A_5]: (r1_xboole_0(A_5, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_8])).
% 2.19/1.36  tff(c_261, plain, (![A_45, B_46]: (~r2_hidden(A_45, B_46) | ~r1_xboole_0(k1_tarski(A_45), B_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.19/1.36  tff(c_269, plain, (![A_45]: (~r2_hidden(A_45, '#skF_4'))), inference(resolution, [status(thm)], [c_194, c_261])).
% 2.19/1.36  tff(c_90, plain, (![A_32]: (k2_tarski(A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.36  tff(c_14, plain, (![D_13, A_8]: (r2_hidden(D_13, k2_tarski(A_8, D_13)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.19/1.36  tff(c_102, plain, (![A_33]: (r2_hidden(A_33, k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_90, c_14])).
% 2.19/1.36  tff(c_105, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_102])).
% 2.19/1.36  tff(c_189, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_105])).
% 2.19/1.36  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_189])).
% 2.19/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.36  
% 2.19/1.36  Inference rules
% 2.19/1.36  ----------------------
% 2.19/1.36  #Ref     : 0
% 2.19/1.36  #Sup     : 58
% 2.19/1.36  #Fact    : 0
% 2.19/1.36  #Define  : 0
% 2.19/1.36  #Split   : 0
% 2.19/1.36  #Chain   : 0
% 2.19/1.36  #Close   : 0
% 2.19/1.36  
% 2.19/1.36  Ordering : KBO
% 2.19/1.36  
% 2.19/1.36  Simplification rules
% 2.19/1.36  ----------------------
% 2.19/1.36  #Subsume      : 0
% 2.19/1.36  #Demod        : 26
% 2.19/1.36  #Tautology    : 41
% 2.19/1.36  #SimpNegUnit  : 1
% 2.19/1.36  #BackRed      : 9
% 2.19/1.36  
% 2.19/1.36  #Partial instantiations: 0
% 2.19/1.36  #Strategies tried      : 1
% 2.19/1.36  
% 2.19/1.36  Timing (in seconds)
% 2.19/1.36  ----------------------
% 2.19/1.36  Preprocessing        : 0.33
% 2.19/1.36  Parsing              : 0.15
% 2.19/1.36  CNF conversion       : 0.03
% 2.19/1.36  Main loop            : 0.19
% 2.19/1.36  Inferencing          : 0.06
% 2.19/1.36  Reduction            : 0.07
% 2.19/1.36  Demodulation         : 0.06
% 2.19/1.36  BG Simplification    : 0.02
% 2.19/1.36  Subsumption          : 0.03
% 2.19/1.36  Abstraction          : 0.02
% 2.19/1.36  MUC search           : 0.00
% 2.19/1.36  Cooper               : 0.00
% 2.19/1.36  Total                : 0.55
% 2.19/1.36  Index Insertion      : 0.00
% 2.19/1.36  Index Deletion       : 0.00
% 2.19/1.36  Index Matching       : 0.00
% 2.19/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
