%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:02 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  44 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   48 (  72 expanded)
%              Number of equality atoms :   27 (  43 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    k1_tarski('#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_44,plain,(
    ! [A_24] : k2_tarski(A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_24] : r2_hidden(A_24,k1_tarski(A_24)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_12])).

tff(c_62,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_34,plain,(
    ! [C_16] :
      ( C_16 = '#skF_5'
      | ~ r2_hidden(C_16,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_72,plain,(
    ! [B_29] :
      ( '#skF_1'('#skF_4',B_29) = '#skF_5'
      | r1_tarski('#skF_4',B_29) ) ),
    inference(resolution,[status(thm)],[c_62,c_34])).

tff(c_136,plain,(
    ! [B_45,A_46] :
      ( k1_tarski(B_45) = A_46
      | k1_xboole_0 = A_46
      | ~ r1_tarski(A_46,k1_tarski(B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_140,plain,(
    ! [B_45] :
      ( k1_tarski(B_45) = '#skF_4'
      | k1_xboole_0 = '#skF_4'
      | '#skF_1'('#skF_4',k1_tarski(B_45)) = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_72,c_136])).

tff(c_165,plain,(
    ! [B_50] :
      ( k1_tarski(B_50) = '#skF_4'
      | '#skF_1'('#skF_4',k1_tarski(B_50)) = '#skF_5' ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_140])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_360,plain,(
    ! [B_71] :
      ( ~ r2_hidden('#skF_5',k1_tarski(B_71))
      | r1_tarski('#skF_4',k1_tarski(B_71))
      | k1_tarski(B_71) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_4])).

tff(c_370,plain,
    ( r1_tarski('#skF_4',k1_tarski('#skF_5'))
    | k1_tarski('#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_50,c_360])).

tff(c_375,plain,(
    r1_tarski('#skF_4',k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_370])).

tff(c_28,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(B_14) = A_13
      | k1_xboole_0 = A_13
      | ~ r1_tarski(A_13,k1_tarski(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_383,plain,
    ( k1_tarski('#skF_5') = '#skF_4'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_375,c_28])).

tff(c_392,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_38,c_383])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:55:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.35  
% 2.14/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.35  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.14/1.35  
% 2.14/1.35  %Foreground sorts:
% 2.14/1.35  
% 2.14/1.35  
% 2.14/1.35  %Background operators:
% 2.14/1.35  
% 2.14/1.35  
% 2.14/1.35  %Foreground operators:
% 2.14/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.14/1.35  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.14/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.14/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.14/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.14/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.35  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.14/1.35  
% 2.14/1.36  tff(f_64, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 2.14/1.36  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.36  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.14/1.36  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.14/1.36  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.14/1.36  tff(c_36, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.36  tff(c_38, plain, (k1_tarski('#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.36  tff(c_44, plain, (![A_24]: (k2_tarski(A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.36  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.36  tff(c_50, plain, (![A_24]: (r2_hidden(A_24, k1_tarski(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_12])).
% 2.14/1.36  tff(c_62, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.36  tff(c_34, plain, (![C_16]: (C_16='#skF_5' | ~r2_hidden(C_16, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.36  tff(c_72, plain, (![B_29]: ('#skF_1'('#skF_4', B_29)='#skF_5' | r1_tarski('#skF_4', B_29))), inference(resolution, [status(thm)], [c_62, c_34])).
% 2.14/1.36  tff(c_136, plain, (![B_45, A_46]: (k1_tarski(B_45)=A_46 | k1_xboole_0=A_46 | ~r1_tarski(A_46, k1_tarski(B_45)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.36  tff(c_140, plain, (![B_45]: (k1_tarski(B_45)='#skF_4' | k1_xboole_0='#skF_4' | '#skF_1'('#skF_4', k1_tarski(B_45))='#skF_5')), inference(resolution, [status(thm)], [c_72, c_136])).
% 2.14/1.36  tff(c_165, plain, (![B_50]: (k1_tarski(B_50)='#skF_4' | '#skF_1'('#skF_4', k1_tarski(B_50))='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_36, c_140])).
% 2.14/1.36  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.14/1.36  tff(c_360, plain, (![B_71]: (~r2_hidden('#skF_5', k1_tarski(B_71)) | r1_tarski('#skF_4', k1_tarski(B_71)) | k1_tarski(B_71)='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_165, c_4])).
% 2.14/1.36  tff(c_370, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5')) | k1_tarski('#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_50, c_360])).
% 2.14/1.36  tff(c_375, plain, (r1_tarski('#skF_4', k1_tarski('#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_38, c_370])).
% 2.14/1.36  tff(c_28, plain, (![B_14, A_13]: (k1_tarski(B_14)=A_13 | k1_xboole_0=A_13 | ~r1_tarski(A_13, k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.36  tff(c_383, plain, (k1_tarski('#skF_5')='#skF_4' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_375, c_28])).
% 2.14/1.36  tff(c_392, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_38, c_383])).
% 2.14/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.36  
% 2.14/1.36  Inference rules
% 2.14/1.36  ----------------------
% 2.14/1.36  #Ref     : 0
% 2.14/1.36  #Sup     : 75
% 2.14/1.36  #Fact    : 0
% 2.14/1.36  #Define  : 0
% 2.14/1.36  #Split   : 2
% 2.14/1.36  #Chain   : 0
% 2.14/1.36  #Close   : 0
% 2.14/1.36  
% 2.14/1.36  Ordering : KBO
% 2.14/1.36  
% 2.14/1.36  Simplification rules
% 2.14/1.36  ----------------------
% 2.14/1.36  #Subsume      : 9
% 2.14/1.36  #Demod        : 14
% 2.14/1.36  #Tautology    : 36
% 2.14/1.36  #SimpNegUnit  : 5
% 2.14/1.36  #BackRed      : 0
% 2.14/1.36  
% 2.14/1.36  #Partial instantiations: 0
% 2.14/1.36  #Strategies tried      : 1
% 2.14/1.36  
% 2.14/1.36  Timing (in seconds)
% 2.14/1.36  ----------------------
% 2.14/1.36  Preprocessing        : 0.32
% 2.14/1.36  Parsing              : 0.16
% 2.14/1.36  CNF conversion       : 0.03
% 2.14/1.36  Main loop            : 0.23
% 2.14/1.36  Inferencing          : 0.09
% 2.14/1.36  Reduction            : 0.07
% 2.14/1.36  Demodulation         : 0.05
% 2.14/1.36  BG Simplification    : 0.02
% 2.14/1.36  Subsumption          : 0.05
% 2.14/1.37  Abstraction          : 0.01
% 2.14/1.37  MUC search           : 0.00
% 2.14/1.37  Cooper               : 0.00
% 2.14/1.37  Total                : 0.58
% 2.14/1.37  Index Insertion      : 0.00
% 2.14/1.37  Index Deletion       : 0.00
% 2.14/1.37  Index Matching       : 0.00
% 2.14/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
