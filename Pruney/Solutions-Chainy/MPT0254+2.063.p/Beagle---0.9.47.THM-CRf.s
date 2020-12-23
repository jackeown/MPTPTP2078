%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   45 (  78 expanded)
%              Number of leaves         :   24 (  37 expanded)
%              Depth                    :   10
%              Number of atoms          :   36 (  77 expanded)
%              Number of equality atoms :   15 (  38 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_99,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_68,plain,(
    ! [A_30,B_31] : r1_tarski(A_30,k2_xboole_0(A_30,B_31)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_68])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_75,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_71,c_8])).

tff(c_77,plain,(
    k2_xboole_0(k1_xboole_0,'#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_40])).

tff(c_114,plain,(
    k2_xboole_0('#skF_4',k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_99,c_77])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_12])).

tff(c_174,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_153,c_8])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_182,plain,(
    ! [A_7] : r1_xboole_0(A_7,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_10])).

tff(c_319,plain,(
    ! [A_47,B_48] :
      ( ~ r2_hidden(A_47,B_48)
      | ~ r1_xboole_0(k1_tarski(A_47),B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_327,plain,(
    ! [A_47] : ~ r2_hidden(A_47,'#skF_4') ),
    inference(resolution,[status(thm)],[c_182,c_319])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_63,plain,(
    ! [D_27,B_28] : r2_hidden(D_27,k2_tarski(D_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_66,plain,(
    ! [A_16] : r2_hidden(A_16,k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_63])).

tff(c_82,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_66])).

tff(c_178,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_82])).

tff(c_329,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_327,c_178])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:36:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.31  
% 2.08/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.32  
% 2.08/1.32  %Foreground sorts:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Background operators:
% 2.08/1.32  
% 2.08/1.32  
% 2.08/1.32  %Foreground operators:
% 2.08/1.32  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.08/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.32  
% 2.08/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.08/1.33  tff(f_65, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.08/1.33  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.08/1.33  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.08/1.33  tff(f_39, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.08/1.33  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.08/1.33  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.08/1.33  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.08/1.33  tff(c_99, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.08/1.33  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.08/1.33  tff(c_68, plain, (![A_30, B_31]: (r1_tarski(A_30, k2_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.33  tff(c_71, plain, (r1_tarski(k1_tarski('#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_68])).
% 2.08/1.33  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.08/1.33  tff(c_75, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_71, c_8])).
% 2.08/1.33  tff(c_77, plain, (k2_xboole_0(k1_xboole_0, '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_75, c_40])).
% 2.08/1.33  tff(c_114, plain, (k2_xboole_0('#skF_4', k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_99, c_77])).
% 2.08/1.33  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.08/1.33  tff(c_153, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_114, c_12])).
% 2.08/1.33  tff(c_174, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_153, c_8])).
% 2.08/1.33  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.08/1.33  tff(c_182, plain, (![A_7]: (r1_xboole_0(A_7, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_10])).
% 2.08/1.33  tff(c_319, plain, (![A_47, B_48]: (~r2_hidden(A_47, B_48) | ~r1_xboole_0(k1_tarski(A_47), B_48))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.08/1.33  tff(c_327, plain, (![A_47]: (~r2_hidden(A_47, '#skF_4'))), inference(resolution, [status(thm)], [c_182, c_319])).
% 2.08/1.33  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.08/1.33  tff(c_63, plain, (![D_27, B_28]: (r2_hidden(D_27, k2_tarski(D_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.33  tff(c_66, plain, (![A_16]: (r2_hidden(A_16, k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_63])).
% 2.08/1.33  tff(c_82, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_75, c_66])).
% 2.08/1.33  tff(c_178, plain, (r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_82])).
% 2.08/1.33  tff(c_329, plain, $false, inference(negUnitSimplification, [status(thm)], [c_327, c_178])).
% 2.08/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.33  
% 2.08/1.33  Inference rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Ref     : 0
% 2.08/1.33  #Sup     : 70
% 2.08/1.33  #Fact    : 0
% 2.08/1.33  #Define  : 0
% 2.08/1.33  #Split   : 0
% 2.08/1.33  #Chain   : 0
% 2.08/1.33  #Close   : 0
% 2.08/1.33  
% 2.08/1.33  Ordering : KBO
% 2.08/1.33  
% 2.08/1.33  Simplification rules
% 2.08/1.33  ----------------------
% 2.08/1.33  #Subsume      : 0
% 2.08/1.33  #Demod        : 42
% 2.08/1.33  #Tautology    : 57
% 2.08/1.33  #SimpNegUnit  : 1
% 2.08/1.33  #BackRed      : 11
% 2.08/1.33  
% 2.08/1.33  #Partial instantiations: 0
% 2.08/1.33  #Strategies tried      : 1
% 2.08/1.33  
% 2.08/1.33  Timing (in seconds)
% 2.08/1.33  ----------------------
% 2.08/1.33  Preprocessing        : 0.32
% 2.08/1.33  Parsing              : 0.16
% 2.08/1.33  CNF conversion       : 0.02
% 2.08/1.33  Main loop            : 0.18
% 2.08/1.33  Inferencing          : 0.06
% 2.08/1.33  Reduction            : 0.07
% 2.08/1.33  Demodulation         : 0.05
% 2.08/1.33  BG Simplification    : 0.01
% 2.08/1.33  Subsumption          : 0.03
% 2.08/1.33  Abstraction          : 0.01
% 2.08/1.33  MUC search           : 0.00
% 2.08/1.33  Cooper               : 0.00
% 2.08/1.33  Total                : 0.52
% 2.08/1.33  Index Insertion      : 0.00
% 2.08/1.33  Index Deletion       : 0.00
% 2.08/1.33  Index Matching       : 0.00
% 2.08/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
