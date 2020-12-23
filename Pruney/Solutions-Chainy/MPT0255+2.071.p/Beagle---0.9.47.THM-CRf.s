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
% DateTime   : Thu Dec  3 09:51:48 EST 2020

% Result     : Theorem 2.38s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  71 expanded)
%              Number of equality atoms :    3 (   6 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_77,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_63,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_150,plain,(
    ! [A_47,B_48] :
      ( r2_hidden('#skF_1'(A_47,B_48),A_47)
      | r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_155,plain,(
    ! [A_47] : r1_tarski(A_47,A_47) ),
    inference(resolution,[status(thm)],[c_150,c_6])).

tff(c_202,plain,(
    ! [A_56,C_57,B_58] :
      ( r2_hidden(A_56,C_57)
      | ~ r1_tarski(k2_tarski(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_208,plain,(
    ! [A_59,B_60] : r2_hidden(A_59,k2_tarski(A_59,B_60)) ),
    inference(resolution,[status(thm)],[c_155,c_202])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [D_40,A_41,B_42] :
      ( ~ r2_hidden(D_40,A_41)
      | r2_hidden(D_40,k2_xboole_0(A_41,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [D_40] :
      ( ~ r2_hidden(D_40,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_40,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_125])).

tff(c_213,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_208,c_135])).

tff(c_34,plain,(
    ! [A_19] : r1_xboole_0(A_19,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_271,plain,(
    ! [A_67,B_68,C_69] :
      ( ~ r1_xboole_0(A_67,B_68)
      | ~ r2_hidden(C_69,B_68)
      | ~ r2_hidden(C_69,A_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_275,plain,(
    ! [C_70,A_71] :
      ( ~ r2_hidden(C_70,k1_xboole_0)
      | ~ r2_hidden(C_70,A_71) ) ),
    inference(resolution,[status(thm)],[c_34,c_271])).

tff(c_303,plain,(
    ! [A_71] : ~ r2_hidden('#skF_5',A_71) ),
    inference(resolution,[status(thm)],[c_213,c_275])).

tff(c_312,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_303,c_213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:51:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.38/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.64  
% 2.38/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.38/1.64  
% 2.38/1.64  %Foreground sorts:
% 2.38/1.64  
% 2.38/1.64  
% 2.38/1.64  %Background operators:
% 2.38/1.64  
% 2.38/1.64  
% 2.38/1.64  %Foreground operators:
% 2.38/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.38/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.38/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.38/1.64  tff('#skF_7', type, '#skF_7': $i).
% 2.38/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.38/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.38/1.64  tff('#skF_5', type, '#skF_5': $i).
% 2.38/1.64  tff('#skF_6', type, '#skF_6': $i).
% 2.38/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.38/1.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.38/1.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.38/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.38/1.64  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.38/1.64  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.38/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.38/1.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.38/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.38/1.64  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.38/1.64  
% 2.38/1.65  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.38/1.65  tff(f_73, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.38/1.65  tff(f_77, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.38/1.65  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 2.38/1.65  tff(f_63, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.38/1.65  tff(f_61, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.38/1.65  tff(c_150, plain, (![A_47, B_48]: (r2_hidden('#skF_1'(A_47, B_48), A_47) | r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.65  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.65  tff(c_155, plain, (![A_47]: (r1_tarski(A_47, A_47))), inference(resolution, [status(thm)], [c_150, c_6])).
% 2.38/1.65  tff(c_202, plain, (![A_56, C_57, B_58]: (r2_hidden(A_56, C_57) | ~r1_tarski(k2_tarski(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.38/1.65  tff(c_208, plain, (![A_59, B_60]: (r2_hidden(A_59, k2_tarski(A_59, B_60)))), inference(resolution, [status(thm)], [c_155, c_202])).
% 2.38/1.65  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.38/1.65  tff(c_125, plain, (![D_40, A_41, B_42]: (~r2_hidden(D_40, A_41) | r2_hidden(D_40, k2_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.38/1.65  tff(c_135, plain, (![D_40]: (~r2_hidden(D_40, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_40, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_125])).
% 2.38/1.65  tff(c_213, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_208, c_135])).
% 2.38/1.65  tff(c_34, plain, (![A_19]: (r1_xboole_0(A_19, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.38/1.65  tff(c_271, plain, (![A_67, B_68, C_69]: (~r1_xboole_0(A_67, B_68) | ~r2_hidden(C_69, B_68) | ~r2_hidden(C_69, A_67))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.38/1.65  tff(c_275, plain, (![C_70, A_71]: (~r2_hidden(C_70, k1_xboole_0) | ~r2_hidden(C_70, A_71))), inference(resolution, [status(thm)], [c_34, c_271])).
% 2.38/1.65  tff(c_303, plain, (![A_71]: (~r2_hidden('#skF_5', A_71))), inference(resolution, [status(thm)], [c_213, c_275])).
% 2.38/1.65  tff(c_312, plain, $false, inference(negUnitSimplification, [status(thm)], [c_303, c_213])).
% 2.38/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.65  
% 2.38/1.65  Inference rules
% 2.38/1.65  ----------------------
% 2.38/1.65  #Ref     : 0
% 2.38/1.65  #Sup     : 63
% 2.38/1.65  #Fact    : 0
% 2.38/1.65  #Define  : 0
% 2.38/1.65  #Split   : 0
% 2.38/1.65  #Chain   : 0
% 2.38/1.65  #Close   : 0
% 2.38/1.65  
% 2.38/1.65  Ordering : KBO
% 2.38/1.65  
% 2.38/1.65  Simplification rules
% 2.38/1.65  ----------------------
% 2.38/1.65  #Subsume      : 8
% 2.38/1.65  #Demod        : 8
% 2.38/1.65  #Tautology    : 22
% 2.38/1.65  #SimpNegUnit  : 2
% 2.38/1.65  #BackRed      : 2
% 2.38/1.65  
% 2.38/1.65  #Partial instantiations: 0
% 2.38/1.65  #Strategies tried      : 1
% 2.38/1.65  
% 2.38/1.65  Timing (in seconds)
% 2.38/1.65  ----------------------
% 2.38/1.65  Preprocessing        : 0.45
% 2.38/1.65  Parsing              : 0.24
% 2.38/1.65  CNF conversion       : 0.03
% 2.38/1.65  Main loop            : 0.29
% 2.38/1.65  Inferencing          : 0.10
% 2.38/1.65  Reduction            : 0.09
% 2.38/1.65  Demodulation         : 0.07
% 2.38/1.66  BG Simplification    : 0.02
% 2.38/1.66  Subsumption          : 0.06
% 2.38/1.66  Abstraction          : 0.02
% 2.38/1.66  MUC search           : 0.00
% 2.38/1.66  Cooper               : 0.00
% 2.38/1.66  Total                : 0.77
% 2.38/1.66  Index Insertion      : 0.00
% 2.38/1.66  Index Deletion       : 0.00
% 2.38/1.66  Index Matching       : 0.00
% 2.38/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
