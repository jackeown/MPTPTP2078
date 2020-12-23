%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:12 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   42 (  58 expanded)
%              Number of equality atoms :   24 (  35 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_62,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
          & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_54,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_112,plain,(
    ! [A_46,B_47] : k1_enumset1(A_46,A_46,B_47) = k2_tarski(A_46,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [E_19,A_13,C_15] : r2_hidden(E_19,k1_enumset1(A_13,E_19,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_130,plain,(
    ! [A_48,B_49] : r2_hidden(A_48,k2_tarski(A_48,B_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_34])).

tff(c_133,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_130])).

tff(c_28,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_145,plain,(
    ! [A_56,B_57] : k5_xboole_0(A_56,k3_xboole_0(A_56,B_57)) = k4_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = k4_xboole_0(A_11,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_145])).

tff(c_160,plain,(
    ! [A_11] : k5_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_157])).

tff(c_62,plain,(
    '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    r1_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_65,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_64])).

tff(c_99,plain,(
    ! [A_44,B_45] :
      ( k3_xboole_0(A_44,B_45) = k1_xboole_0
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_107,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_65,c_99])).

tff(c_154,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_145])).

tff(c_170,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_154])).

tff(c_178,plain,(
    ! [D_59,B_60,A_61] :
      ( ~ r2_hidden(D_59,B_60)
      | ~ r2_hidden(D_59,k4_xboole_0(A_61,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_186,plain,(
    ! [D_64] :
      ( ~ r2_hidden(D_64,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_64,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_170,c_178])).

tff(c_189,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_133,c_186])).

tff(c_193,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_189])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:08:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  
% 1.95/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.19  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.95/1.19  
% 1.95/1.19  %Foreground sorts:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Background operators:
% 1.95/1.19  
% 1.95/1.19  
% 1.95/1.19  %Foreground operators:
% 1.95/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.19  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.19  tff('#skF_6', type, '#skF_6': $i).
% 1.95/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.95/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.95/1.19  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.19  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.95/1.19  
% 1.95/1.20  tff(f_62, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.20  tff(f_64, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.95/1.20  tff(f_60, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.95/1.20  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.95/1.20  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.95/1.20  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.20  tff(f_74, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.95/1.20  tff(f_39, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.95/1.20  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.95/1.20  tff(c_54, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.20  tff(c_112, plain, (![A_46, B_47]: (k1_enumset1(A_46, A_46, B_47)=k2_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.20  tff(c_34, plain, (![E_19, A_13, C_15]: (r2_hidden(E_19, k1_enumset1(A_13, E_19, C_15)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.95/1.20  tff(c_130, plain, (![A_48, B_49]: (r2_hidden(A_48, k2_tarski(A_48, B_49)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_34])).
% 1.95/1.20  tff(c_133, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_130])).
% 1.95/1.20  tff(c_28, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.95/1.20  tff(c_26, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.20  tff(c_145, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k3_xboole_0(A_56, B_57))=k4_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.20  tff(c_157, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=k4_xboole_0(A_11, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_26, c_145])).
% 1.95/1.20  tff(c_160, plain, (![A_11]: (k5_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_157])).
% 1.95/1.20  tff(c_62, plain, ('#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.20  tff(c_64, plain, (r1_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.20  tff(c_65, plain, (r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_64])).
% 1.95/1.20  tff(c_99, plain, (![A_44, B_45]: (k3_xboole_0(A_44, B_45)=k1_xboole_0 | ~r1_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.20  tff(c_107, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_65, c_99])).
% 1.95/1.20  tff(c_154, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_145])).
% 1.95/1.20  tff(c_170, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_160, c_154])).
% 1.95/1.20  tff(c_178, plain, (![D_59, B_60, A_61]: (~r2_hidden(D_59, B_60) | ~r2_hidden(D_59, k4_xboole_0(A_61, B_60)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.95/1.20  tff(c_186, plain, (![D_64]: (~r2_hidden(D_64, k1_tarski('#skF_6')) | ~r2_hidden(D_64, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_170, c_178])).
% 1.95/1.20  tff(c_189, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_133, c_186])).
% 1.95/1.20  tff(c_193, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_133, c_189])).
% 1.95/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  Inference rules
% 1.95/1.20  ----------------------
% 1.95/1.20  #Ref     : 0
% 1.95/1.20  #Sup     : 32
% 1.95/1.20  #Fact    : 0
% 1.95/1.20  #Define  : 0
% 1.95/1.20  #Split   : 0
% 1.95/1.20  #Chain   : 0
% 1.95/1.20  #Close   : 0
% 2.01/1.20  
% 2.01/1.20  Ordering : KBO
% 2.01/1.20  
% 2.01/1.20  Simplification rules
% 2.01/1.20  ----------------------
% 2.01/1.20  #Subsume      : 0
% 2.01/1.20  #Demod        : 6
% 2.01/1.20  #Tautology    : 23
% 2.01/1.20  #SimpNegUnit  : 0
% 2.01/1.20  #BackRed      : 0
% 2.01/1.20  
% 2.01/1.20  #Partial instantiations: 0
% 2.01/1.20  #Strategies tried      : 1
% 2.01/1.20  
% 2.01/1.20  Timing (in seconds)
% 2.01/1.20  ----------------------
% 2.01/1.20  Preprocessing        : 0.31
% 2.01/1.20  Parsing              : 0.15
% 2.01/1.20  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.14
% 2.01/1.21  Inferencing          : 0.04
% 2.01/1.21  Reduction            : 0.05
% 2.01/1.21  Demodulation         : 0.04
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.03
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.48
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
