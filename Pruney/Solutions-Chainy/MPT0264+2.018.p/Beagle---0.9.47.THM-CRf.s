%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:23 EST 2020

% Result     : Theorem 2.10s
% Output     : CNFRefutation 2.10s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_54,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_56,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_36,plain,(
    ! [D_19,A_14] : r2_hidden(D_19,k2_tarski(A_14,D_19)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    k3_xboole_0(k2_tarski('#skF_7','#skF_8'),'#skF_9') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_172,plain,(
    ! [D_43,A_44,B_45] :
      ( r2_hidden(D_43,k3_xboole_0(A_44,B_45))
      | ~ r2_hidden(D_43,B_45)
      | ~ r2_hidden(D_43,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_437,plain,(
    ! [D_570] :
      ( r2_hidden(D_570,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_570,'#skF_9')
      | ~ r2_hidden(D_570,k2_tarski('#skF_7','#skF_8')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_172])).

tff(c_461,plain,
    ( r2_hidden('#skF_8',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_437])).

tff(c_470,plain,(
    r2_hidden('#skF_8',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_461])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_479,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_470,c_22])).

tff(c_517,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:07:09 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.10/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  
% 2.10/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.31  %$ r2_hidden > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.10/1.31  
% 2.10/1.31  %Foreground sorts:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Background operators:
% 2.10/1.31  
% 2.10/1.31  
% 2.10/1.31  %Foreground operators:
% 2.10/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.10/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.10/1.31  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.10/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.10/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.10/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.10/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.10/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.10/1.31  tff('#skF_9', type, '#skF_9': $i).
% 2.10/1.31  tff('#skF_8', type, '#skF_8': $i).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.10/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.10/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.10/1.31  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.10/1.31  
% 2.10/1.32  tff(f_67, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 2.10/1.32  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.10/1.32  tff(f_36, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.10/1.32  tff(f_43, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.10/1.32  tff(c_54, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.32  tff(c_56, plain, (r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.32  tff(c_36, plain, (![D_19, A_14]: (r2_hidden(D_19, k2_tarski(A_14, D_19)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.10/1.32  tff(c_58, plain, (k3_xboole_0(k2_tarski('#skF_7', '#skF_8'), '#skF_9')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.10/1.32  tff(c_172, plain, (![D_43, A_44, B_45]: (r2_hidden(D_43, k3_xboole_0(A_44, B_45)) | ~r2_hidden(D_43, B_45) | ~r2_hidden(D_43, A_44))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.10/1.32  tff(c_437, plain, (![D_570]: (r2_hidden(D_570, k1_tarski('#skF_7')) | ~r2_hidden(D_570, '#skF_9') | ~r2_hidden(D_570, k2_tarski('#skF_7', '#skF_8')))), inference(superposition, [status(thm), theory('equality')], [c_58, c_172])).
% 2.10/1.32  tff(c_461, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7')) | ~r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_36, c_437])).
% 2.10/1.32  tff(c_470, plain, (r2_hidden('#skF_8', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_461])).
% 2.10/1.32  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.10/1.32  tff(c_479, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_470, c_22])).
% 2.10/1.32  tff(c_517, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_479])).
% 2.10/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.10/1.32  
% 2.10/1.32  Inference rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Ref     : 0
% 2.10/1.32  #Sup     : 68
% 2.10/1.32  #Fact    : 0
% 2.10/1.32  #Define  : 0
% 2.10/1.32  #Split   : 0
% 2.10/1.32  #Chain   : 0
% 2.10/1.32  #Close   : 0
% 2.10/1.32  
% 2.10/1.32  Ordering : KBO
% 2.10/1.32  
% 2.10/1.32  Simplification rules
% 2.10/1.32  ----------------------
% 2.10/1.32  #Subsume      : 10
% 2.10/1.32  #Demod        : 7
% 2.10/1.32  #Tautology    : 25
% 2.10/1.32  #SimpNegUnit  : 1
% 2.10/1.32  #BackRed      : 0
% 2.10/1.32  
% 2.10/1.32  #Partial instantiations: 300
% 2.10/1.32  #Strategies tried      : 1
% 2.10/1.32  
% 2.10/1.32  Timing (in seconds)
% 2.10/1.32  ----------------------
% 2.10/1.32  Preprocessing        : 0.29
% 2.10/1.32  Parsing              : 0.14
% 2.10/1.32  CNF conversion       : 0.02
% 2.44/1.32  Main loop            : 0.25
% 2.44/1.32  Inferencing          : 0.11
% 2.44/1.32  Reduction            : 0.07
% 2.44/1.32  Demodulation         : 0.06
% 2.44/1.32  BG Simplification    : 0.02
% 2.44/1.32  Subsumption          : 0.04
% 2.44/1.32  Abstraction          : 0.01
% 2.44/1.32  MUC search           : 0.00
% 2.44/1.32  Cooper               : 0.00
% 2.44/1.32  Total                : 0.56
% 2.44/1.32  Index Insertion      : 0.00
% 2.44/1.32  Index Deletion       : 0.00
% 2.44/1.32  Index Matching       : 0.00
% 2.44/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
