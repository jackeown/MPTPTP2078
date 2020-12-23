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
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   51 (  92 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 ( 107 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(A)
     => ~ v1_xboole_0(k2_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_xboole_0)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_56,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_46,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_42,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_12,plain,(
    ! [B_10,A_9] :
      ( ~ v1_xboole_0(k2_xboole_0(B_10,A_9))
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_102,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_12])).

tff(c_118,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_102])).

tff(c_6,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_118,c_6])).

tff(c_16,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [A_12] : r1_xboole_0(A_12,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_16])).

tff(c_14,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_135,plain,(
    ! [A_11] : k3_xboole_0(A_11,'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_132,c_14])).

tff(c_232,plain,(
    ! [A_46,B_47,C_48] :
      ( ~ r1_xboole_0(A_46,B_47)
      | ~ r2_hidden(C_48,k3_xboole_0(A_46,B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_235,plain,(
    ! [A_11,C_48] :
      ( ~ r1_xboole_0(A_11,'#skF_6')
      | ~ r2_hidden(C_48,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_232])).

tff(c_237,plain,(
    ! [C_48] : ~ r2_hidden(C_48,'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_137,c_235])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_115,plain,(
    k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_123,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_12])).

tff(c_127,plain,(
    v1_xboole_0(k2_tarski('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_123])).

tff(c_161,plain,(
    ! [A_41] :
      ( A_41 = '#skF_6'
      | ~ v1_xboole_0(A_41) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_6])).

tff(c_168,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_127,c_161])).

tff(c_22,plain,(
    ! [D_18,B_14] : r2_hidden(D_18,k2_tarski(D_18,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_182,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_22])).

tff(c_240,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_237,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.32  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.12/1.32  
% 2.12/1.32  %Foreground sorts:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Background operators:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Foreground operators:
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.12/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.32  
% 2.12/1.33  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.33  tff(f_75, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.12/1.33  tff(f_52, axiom, (![A, B]: (~v1_xboole_0(A) => ~v1_xboole_0(k2_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc5_xboole_0)).
% 2.12/1.33  tff(f_32, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.12/1.33  tff(f_56, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.12/1.33  tff(f_54, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.12/1.33  tff(f_46, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.12/1.33  tff(f_65, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.12/1.33  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.12/1.33  tff(c_42, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.12/1.33  tff(c_12, plain, (![B_10, A_9]: (~v1_xboole_0(k2_xboole_0(B_10, A_9)) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.12/1.33  tff(c_102, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_42, c_12])).
% 2.12/1.33  tff(c_118, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_102])).
% 2.12/1.33  tff(c_6, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.12/1.33  tff(c_132, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_118, c_6])).
% 2.12/1.33  tff(c_16, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.33  tff(c_137, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_16])).
% 2.12/1.33  tff(c_14, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.12/1.33  tff(c_135, plain, (![A_11]: (k3_xboole_0(A_11, '#skF_6')='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_132, c_132, c_14])).
% 2.12/1.33  tff(c_232, plain, (![A_46, B_47, C_48]: (~r1_xboole_0(A_46, B_47) | ~r2_hidden(C_48, k3_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.12/1.33  tff(c_235, plain, (![A_11, C_48]: (~r1_xboole_0(A_11, '#skF_6') | ~r2_hidden(C_48, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_232])).
% 2.12/1.33  tff(c_237, plain, (![C_48]: (~r2_hidden(C_48, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_137, c_235])).
% 2.12/1.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.33  tff(c_115, plain, (k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_42])).
% 2.12/1.33  tff(c_123, plain, (~v1_xboole_0(k1_xboole_0) | v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_12])).
% 2.12/1.33  tff(c_127, plain, (v1_xboole_0(k2_tarski('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_123])).
% 2.12/1.33  tff(c_161, plain, (![A_41]: (A_41='#skF_6' | ~v1_xboole_0(A_41))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_6])).
% 2.12/1.33  tff(c_168, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_127, c_161])).
% 2.12/1.33  tff(c_22, plain, (![D_18, B_14]: (r2_hidden(D_18, k2_tarski(D_18, B_14)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.12/1.33  tff(c_182, plain, (r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_168, c_22])).
% 2.12/1.33  tff(c_240, plain, $false, inference(negUnitSimplification, [status(thm)], [c_237, c_182])).
% 2.12/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.33  
% 2.12/1.33  Inference rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Ref     : 0
% 2.12/1.33  #Sup     : 50
% 2.12/1.33  #Fact    : 0
% 2.12/1.33  #Define  : 0
% 2.12/1.33  #Split   : 1
% 2.12/1.33  #Chain   : 0
% 2.12/1.33  #Close   : 0
% 2.12/1.33  
% 2.12/1.33  Ordering : KBO
% 2.12/1.33  
% 2.12/1.33  Simplification rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Subsume      : 4
% 2.12/1.33  #Demod        : 29
% 2.12/1.33  #Tautology    : 38
% 2.12/1.33  #SimpNegUnit  : 2
% 2.12/1.33  #BackRed      : 9
% 2.12/1.33  
% 2.12/1.33  #Partial instantiations: 0
% 2.12/1.33  #Strategies tried      : 1
% 2.12/1.33  
% 2.12/1.33  Timing (in seconds)
% 2.12/1.33  ----------------------
% 2.12/1.33  Preprocessing        : 0.30
% 2.12/1.33  Parsing              : 0.15
% 2.12/1.33  CNF conversion       : 0.02
% 2.12/1.33  Main loop            : 0.22
% 2.12/1.33  Inferencing          : 0.07
% 2.12/1.33  Reduction            : 0.08
% 2.12/1.33  Demodulation         : 0.07
% 2.12/1.33  BG Simplification    : 0.01
% 2.12/1.33  Subsumption          : 0.04
% 2.12/1.33  Abstraction          : 0.01
% 2.12/1.33  MUC search           : 0.00
% 2.12/1.33  Cooper               : 0.00
% 2.12/1.33  Total                : 0.55
% 2.12/1.33  Index Insertion      : 0.00
% 2.12/1.33  Index Deletion       : 0.00
% 2.12/1.33  Index Matching       : 0.00
% 2.12/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
