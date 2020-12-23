%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   47 (  84 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   56 ( 120 expanded)
%              Number of equality atoms :   31 (  74 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_32,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_54,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_56,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_118,plain,(
    ! [B_47,A_48] :
      ( k1_tarski(B_47) = A_48
      | k1_xboole_0 = A_48
      | ~ r1_tarski(A_48,k1_tarski(B_47)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_128,plain,
    ( k1_tarski('#skF_3') = k1_tarski('#skF_4')
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_56,c_118])).

tff(c_133,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_40,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_80,plain,(
    ! [A_37,B_38] : k1_enumset1(A_37,A_37,B_38) = k2_tarski(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [E_11,B_6,C_7] : r2_hidden(E_11,k1_enumset1(E_11,B_6,C_7)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_98,plain,(
    ! [A_39,B_40] : r2_hidden(A_39,k2_tarski(A_39,B_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_22])).

tff(c_101,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_98])).

tff(c_142,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_101])).

tff(c_14,plain,(
    ! [A_4] : k5_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_185,plain,(
    ! [A_60,C_61,B_62] :
      ( ~ r2_hidden(A_60,C_61)
      | ~ r2_hidden(A_60,B_62)
      | ~ r2_hidden(A_60,k5_xboole_0(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_193,plain,(
    ! [A_63,A_64] :
      ( ~ r2_hidden(A_63,k1_xboole_0)
      | ~ r2_hidden(A_63,A_64)
      | ~ r2_hidden(A_63,A_64) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_185])).

tff(c_196,plain,(
    ! [A_64] : ~ r2_hidden('#skF_3',A_64) ),
    inference(resolution,[status(thm)],[c_142,c_193])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_142])).

tff(c_199,plain,(
    k1_tarski('#skF_3') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_210,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_101])).

tff(c_42,plain,(
    ! [A_13,B_14] : k1_enumset1(A_13,A_13,B_14) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_269,plain,(
    ! [E_85,C_86,B_87,A_88] :
      ( E_85 = C_86
      | E_85 = B_87
      | E_85 = A_88
      | ~ r2_hidden(E_85,k1_enumset1(A_88,B_87,C_86)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_288,plain,(
    ! [E_89,B_90,A_91] :
      ( E_89 = B_90
      | E_89 = A_91
      | E_89 = A_91
      | ~ r2_hidden(E_89,k2_tarski(A_91,B_90)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_269])).

tff(c_302,plain,(
    ! [E_92,A_93] :
      ( E_92 = A_93
      | E_92 = A_93
      | E_92 = A_93
      | ~ r2_hidden(E_92,k1_tarski(A_93)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_288])).

tff(c_305,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_210,c_302])).

tff(c_315,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_54,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:16:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  
% 2.15/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.15/1.28  
% 2.15/1.28  %Foreground sorts:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Background operators:
% 2.15/1.28  
% 2.15/1.28  
% 2.15/1.28  %Foreground operators:
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.15/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.15/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.15/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.15/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.15/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.15/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.15/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.15/1.28  
% 2.15/1.29  tff(f_68, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.15/1.29  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.15/1.29  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.15/1.29  tff(f_53, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.15/1.29  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.15/1.29  tff(f_34, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.15/1.29  tff(f_32, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 2.15/1.29  tff(c_54, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.15/1.29  tff(c_56, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.15/1.29  tff(c_118, plain, (![B_47, A_48]: (k1_tarski(B_47)=A_48 | k1_xboole_0=A_48 | ~r1_tarski(A_48, k1_tarski(B_47)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.29  tff(c_128, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4') | k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_56, c_118])).
% 2.15/1.29  tff(c_133, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_128])).
% 2.15/1.29  tff(c_40, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.15/1.29  tff(c_80, plain, (![A_37, B_38]: (k1_enumset1(A_37, A_37, B_38)=k2_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_22, plain, (![E_11, B_6, C_7]: (r2_hidden(E_11, k1_enumset1(E_11, B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_98, plain, (![A_39, B_40]: (r2_hidden(A_39, k2_tarski(A_39, B_40)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_22])).
% 2.15/1.29  tff(c_101, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_98])).
% 2.15/1.29  tff(c_142, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_133, c_101])).
% 2.15/1.29  tff(c_14, plain, (![A_4]: (k5_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.15/1.29  tff(c_185, plain, (![A_60, C_61, B_62]: (~r2_hidden(A_60, C_61) | ~r2_hidden(A_60, B_62) | ~r2_hidden(A_60, k5_xboole_0(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.15/1.29  tff(c_193, plain, (![A_63, A_64]: (~r2_hidden(A_63, k1_xboole_0) | ~r2_hidden(A_63, A_64) | ~r2_hidden(A_63, A_64))), inference(superposition, [status(thm), theory('equality')], [c_14, c_185])).
% 2.15/1.29  tff(c_196, plain, (![A_64]: (~r2_hidden('#skF_3', A_64))), inference(resolution, [status(thm)], [c_142, c_193])).
% 2.15/1.29  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_142])).
% 2.15/1.29  tff(c_199, plain, (k1_tarski('#skF_3')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_128])).
% 2.15/1.29  tff(c_210, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_199, c_101])).
% 2.15/1.29  tff(c_42, plain, (![A_13, B_14]: (k1_enumset1(A_13, A_13, B_14)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.15/1.29  tff(c_269, plain, (![E_85, C_86, B_87, A_88]: (E_85=C_86 | E_85=B_87 | E_85=A_88 | ~r2_hidden(E_85, k1_enumset1(A_88, B_87, C_86)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.29  tff(c_288, plain, (![E_89, B_90, A_91]: (E_89=B_90 | E_89=A_91 | E_89=A_91 | ~r2_hidden(E_89, k2_tarski(A_91, B_90)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_269])).
% 2.15/1.29  tff(c_302, plain, (![E_92, A_93]: (E_92=A_93 | E_92=A_93 | E_92=A_93 | ~r2_hidden(E_92, k1_tarski(A_93)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_288])).
% 2.15/1.29  tff(c_305, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_210, c_302])).
% 2.15/1.29  tff(c_315, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_54, c_305])).
% 2.15/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.29  
% 2.15/1.29  Inference rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Ref     : 0
% 2.15/1.29  #Sup     : 59
% 2.15/1.29  #Fact    : 0
% 2.15/1.29  #Define  : 0
% 2.15/1.29  #Split   : 1
% 2.15/1.29  #Chain   : 0
% 2.15/1.29  #Close   : 0
% 2.15/1.29  
% 2.15/1.29  Ordering : KBO
% 2.15/1.29  
% 2.15/1.29  Simplification rules
% 2.15/1.29  ----------------------
% 2.15/1.29  #Subsume      : 1
% 2.15/1.29  #Demod        : 17
% 2.15/1.29  #Tautology    : 45
% 2.15/1.29  #SimpNegUnit  : 2
% 2.15/1.29  #BackRed      : 4
% 2.15/1.29  
% 2.15/1.29  #Partial instantiations: 0
% 2.15/1.29  #Strategies tried      : 1
% 2.15/1.29  
% 2.15/1.29  Timing (in seconds)
% 2.15/1.29  ----------------------
% 2.15/1.29  Preprocessing        : 0.32
% 2.15/1.29  Parsing              : 0.16
% 2.15/1.29  CNF conversion       : 0.02
% 2.15/1.30  Main loop            : 0.22
% 2.15/1.30  Inferencing          : 0.08
% 2.15/1.30  Reduction            : 0.07
% 2.15/1.30  Demodulation         : 0.05
% 2.15/1.30  BG Simplification    : 0.02
% 2.15/1.30  Subsumption          : 0.04
% 2.15/1.30  Abstraction          : 0.01
% 2.15/1.30  MUC search           : 0.00
% 2.15/1.30  Cooper               : 0.00
% 2.15/1.30  Total                : 0.57
% 2.15/1.30  Index Insertion      : 0.00
% 2.15/1.30  Index Deletion       : 0.00
% 2.15/1.30  Index Matching       : 0.00
% 2.15/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
