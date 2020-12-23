%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:30 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   46 ( 109 expanded)
%              Number of leaves         :   23 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 ( 213 expanded)
%              Number of equality atoms :   22 (  98 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_46,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    k2_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    ! [D_53,B_54,A_55] :
      ( ~ r2_hidden(D_53,B_54)
      | r2_hidden(D_53,k2_xboole_0(A_55,B_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_213,plain,(
    ! [D_56] :
      ( ~ r2_hidden(D_56,'#skF_6')
      | r2_hidden(D_56,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_201])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_264,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_64,k1_tarski('#skF_4')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_213,c_4])).

tff(c_269,plain,(
    r1_tarski('#skF_6',k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_38,plain,(
    ! [B_23,A_22] :
      ( k1_tarski(B_23) = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,k1_tarski(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_272,plain,
    ( k1_tarski('#skF_4') = '#skF_6'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_269,c_38])).

tff(c_278,plain,(
    k1_tarski('#skF_4') = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_272])).

tff(c_162,plain,(
    ! [D_43,A_44,B_45] :
      ( ~ r2_hidden(D_43,A_44)
      | r2_hidden(D_43,k2_xboole_0(A_44,B_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_168,plain,(
    ! [D_43] :
      ( ~ r2_hidden(D_43,'#skF_5')
      | r2_hidden(D_43,k1_tarski('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_162])).

tff(c_171,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden('#skF_1'(A_49,B_50),B_50)
      | r1_tarski(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_185,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_49,k1_tarski('#skF_4')),'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_168,c_171])).

tff(c_423,plain,(
    ! [A_74] :
      ( r1_tarski(A_74,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_74,'#skF_6'),'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_278,c_185])).

tff(c_428,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_423])).

tff(c_293,plain,(
    ! [A_22] :
      ( k1_tarski('#skF_4') = A_22
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_278,c_38])).

tff(c_306,plain,(
    ! [A_22] :
      ( A_22 = '#skF_6'
      | k1_xboole_0 = A_22
      | ~ r1_tarski(A_22,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_293])).

tff(c_431,plain,
    ( '#skF_5' = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_428,c_306])).

tff(c_438,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_50,c_431])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:22:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.29  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.06/1.29  
% 2.06/1.29  %Foreground sorts:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Background operators:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Foreground operators:
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.29  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.06/1.29  
% 2.06/1.30  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.06/1.30  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.30  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.06/1.30  tff(f_59, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.06/1.30  tff(c_48, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.30  tff(c_50, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.30  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.30  tff(c_46, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.30  tff(c_52, plain, (k2_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.06/1.30  tff(c_201, plain, (![D_53, B_54, A_55]: (~r2_hidden(D_53, B_54) | r2_hidden(D_53, k2_xboole_0(A_55, B_54)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.30  tff(c_213, plain, (![D_56]: (~r2_hidden(D_56, '#skF_6') | r2_hidden(D_56, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_201])).
% 2.06/1.30  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.30  tff(c_264, plain, (![A_64]: (r1_tarski(A_64, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_64, k1_tarski('#skF_4')), '#skF_6'))), inference(resolution, [status(thm)], [c_213, c_4])).
% 2.06/1.30  tff(c_269, plain, (r1_tarski('#skF_6', k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_264])).
% 2.06/1.30  tff(c_38, plain, (![B_23, A_22]: (k1_tarski(B_23)=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, k1_tarski(B_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.06/1.30  tff(c_272, plain, (k1_tarski('#skF_4')='#skF_6' | k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_269, c_38])).
% 2.06/1.30  tff(c_278, plain, (k1_tarski('#skF_4')='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_46, c_272])).
% 2.06/1.30  tff(c_162, plain, (![D_43, A_44, B_45]: (~r2_hidden(D_43, A_44) | r2_hidden(D_43, k2_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.30  tff(c_168, plain, (![D_43]: (~r2_hidden(D_43, '#skF_5') | r2_hidden(D_43, k1_tarski('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_162])).
% 2.06/1.30  tff(c_171, plain, (![A_49, B_50]: (~r2_hidden('#skF_1'(A_49, B_50), B_50) | r1_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.30  tff(c_185, plain, (![A_49]: (r1_tarski(A_49, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_49, k1_tarski('#skF_4')), '#skF_5'))), inference(resolution, [status(thm)], [c_168, c_171])).
% 2.06/1.30  tff(c_423, plain, (![A_74]: (r1_tarski(A_74, '#skF_6') | ~r2_hidden('#skF_1'(A_74, '#skF_6'), '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_278, c_185])).
% 2.06/1.30  tff(c_428, plain, (r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_423])).
% 2.06/1.30  tff(c_293, plain, (![A_22]: (k1_tarski('#skF_4')=A_22 | k1_xboole_0=A_22 | ~r1_tarski(A_22, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_278, c_38])).
% 2.06/1.30  tff(c_306, plain, (![A_22]: (A_22='#skF_6' | k1_xboole_0=A_22 | ~r1_tarski(A_22, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_278, c_293])).
% 2.06/1.30  tff(c_431, plain, ('#skF_5'='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_428, c_306])).
% 2.06/1.30  tff(c_438, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_50, c_431])).
% 2.06/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  Inference rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Ref     : 0
% 2.06/1.30  #Sup     : 97
% 2.06/1.30  #Fact    : 0
% 2.06/1.30  #Define  : 0
% 2.06/1.30  #Split   : 0
% 2.06/1.30  #Chain   : 0
% 2.06/1.30  #Close   : 0
% 2.06/1.30  
% 2.06/1.30  Ordering : KBO
% 2.06/1.30  
% 2.06/1.30  Simplification rules
% 2.06/1.30  ----------------------
% 2.06/1.30  #Subsume      : 5
% 2.06/1.30  #Demod        : 19
% 2.06/1.30  #Tautology    : 56
% 2.06/1.30  #SimpNegUnit  : 4
% 2.06/1.30  #BackRed      : 5
% 2.06/1.30  
% 2.06/1.30  #Partial instantiations: 0
% 2.06/1.30  #Strategies tried      : 1
% 2.06/1.30  
% 2.06/1.30  Timing (in seconds)
% 2.06/1.30  ----------------------
% 2.06/1.30  Preprocessing        : 0.30
% 2.06/1.30  Parsing              : 0.16
% 2.06/1.30  CNF conversion       : 0.02
% 2.06/1.30  Main loop            : 0.23
% 2.06/1.30  Inferencing          : 0.09
% 2.06/1.30  Reduction            : 0.07
% 2.06/1.30  Demodulation         : 0.05
% 2.06/1.30  BG Simplification    : 0.01
% 2.06/1.30  Subsumption          : 0.04
% 2.06/1.30  Abstraction          : 0.01
% 2.06/1.30  MUC search           : 0.00
% 2.06/1.30  Cooper               : 0.00
% 2.06/1.30  Total                : 0.56
% 2.06/1.30  Index Insertion      : 0.00
% 2.06/1.30  Index Deletion       : 0.00
% 2.06/1.30  Index Matching       : 0.00
% 2.06/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
