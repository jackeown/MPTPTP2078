%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:27 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  40 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [D_22,B_23] : r2_hidden(D_22,k2_tarski(D_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_58])).

tff(c_48,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,(
    ! [D_31,B_32,A_33] :
      ( r2_hidden(D_31,B_32)
      | ~ r2_hidden(D_31,k3_xboole_0(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_100,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_34,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_96])).

tff(c_105,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_61,c_100])).

tff(c_119,plain,(
    ! [D_41,B_42,A_43] :
      ( D_41 = B_42
      | D_41 = A_43
      | ~ r2_hidden(D_41,k2_tarski(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_133,plain,(
    ! [D_44,A_45] :
      ( D_44 = A_45
      | D_44 = A_45
      | ~ r2_hidden(D_44,k1_tarski(A_45)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_119])).

tff(c_136,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_105,c_133])).

tff(c_143,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:11:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.80/1.22  
% 1.80/1.22  %Foreground sorts:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Background operators:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Foreground operators:
% 1.80/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.80/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.80/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.80/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.22  
% 1.93/1.23  tff(f_56, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.93/1.23  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.23  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.23  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.93/1.23  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.23  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.93/1.23  tff(c_58, plain, (![D_22, B_23]: (r2_hidden(D_22, k2_tarski(D_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.23  tff(c_61, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_58])).
% 1.93/1.23  tff(c_48, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.93/1.23  tff(c_96, plain, (![D_31, B_32, A_33]: (r2_hidden(D_31, B_32) | ~r2_hidden(D_31, k3_xboole_0(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.23  tff(c_100, plain, (![D_34]: (r2_hidden(D_34, k1_tarski('#skF_6')) | ~r2_hidden(D_34, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_48, c_96])).
% 1.93/1.23  tff(c_105, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_61, c_100])).
% 1.93/1.23  tff(c_119, plain, (![D_41, B_42, A_43]: (D_41=B_42 | D_41=A_43 | ~r2_hidden(D_41, k2_tarski(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.93/1.23  tff(c_133, plain, (![D_44, A_45]: (D_44=A_45 | D_44=A_45 | ~r2_hidden(D_44, k1_tarski(A_45)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_119])).
% 1.93/1.23  tff(c_136, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_105, c_133])).
% 1.93/1.23  tff(c_143, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_136])).
% 1.93/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.23  
% 1.93/1.23  Inference rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Ref     : 0
% 1.93/1.23  #Sup     : 22
% 1.93/1.23  #Fact    : 0
% 1.93/1.23  #Define  : 0
% 1.93/1.23  #Split   : 0
% 1.93/1.23  #Chain   : 0
% 1.93/1.23  #Close   : 0
% 1.93/1.23  
% 1.93/1.23  Ordering : KBO
% 1.93/1.23  
% 1.93/1.23  Simplification rules
% 1.93/1.23  ----------------------
% 1.93/1.23  #Subsume      : 0
% 1.93/1.23  #Demod        : 1
% 1.93/1.23  #Tautology    : 14
% 1.93/1.23  #SimpNegUnit  : 1
% 1.93/1.23  #BackRed      : 0
% 1.93/1.23  
% 1.93/1.23  #Partial instantiations: 0
% 1.93/1.23  #Strategies tried      : 1
% 1.93/1.23  
% 1.93/1.23  Timing (in seconds)
% 1.93/1.23  ----------------------
% 1.93/1.23  Preprocessing        : 0.31
% 1.93/1.23  Parsing              : 0.16
% 1.93/1.23  CNF conversion       : 0.02
% 1.93/1.23  Main loop            : 0.12
% 1.93/1.23  Inferencing          : 0.04
% 1.93/1.23  Reduction            : 0.04
% 1.93/1.23  Demodulation         : 0.03
% 1.93/1.23  BG Simplification    : 0.01
% 1.93/1.23  Subsumption          : 0.02
% 1.93/1.23  Abstraction          : 0.01
% 1.93/1.23  MUC search           : 0.00
% 1.93/1.23  Cooper               : 0.00
% 1.93/1.23  Total                : 0.45
% 1.93/1.23  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
