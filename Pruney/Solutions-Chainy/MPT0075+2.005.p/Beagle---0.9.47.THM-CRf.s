%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:30 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   32 (  39 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  67 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ~ v1_xboole_0(C)
       => ~ ( r1_tarski(C,A)
            & r1_tarski(C,B)
            & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
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

tff(c_24,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_22,plain,(
    r1_tarski('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_20,plain,(
    r1_tarski('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_56,plain,(
    ! [C_33,B_34,A_35] :
      ( r2_hidden(C_33,B_34)
      | ~ r2_hidden(C_33,A_35)
      | ~ r1_tarski(A_35,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_68,plain,(
    ! [A_1,B_34] :
      ( r2_hidden('#skF_1'(A_1),B_34)
      | ~ r1_tarski(A_1,B_34)
      | v1_xboole_0(A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_118,plain,(
    ! [A_43,B_44] :
      ( r2_hidden('#skF_1'(A_43),B_44)
      | ~ r1_tarski(A_43,B_44)
      | v1_xboole_0(A_43) ) ),
    inference(resolution,[status(thm)],[c_4,c_56])).

tff(c_18,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_69,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [C_38] :
      ( ~ r2_hidden(C_38,'#skF_5')
      | ~ r2_hidden(C_38,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_18,c_69])).

tff(c_167,plain,(
    ! [A_49] :
      ( ~ r2_hidden('#skF_1'(A_49),'#skF_4')
      | ~ r1_tarski(A_49,'#skF_5')
      | v1_xboole_0(A_49) ) ),
    inference(resolution,[status(thm)],[c_118,c_78])).

tff(c_251,plain,(
    ! [A_61] :
      ( ~ r1_tarski(A_61,'#skF_5')
      | ~ r1_tarski(A_61,'#skF_4')
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_68,c_167])).

tff(c_262,plain,
    ( ~ r1_tarski('#skF_6','#skF_4')
    | v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_251])).

tff(c_268,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_262])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_268])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:06:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.24  
% 2.03/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_4 > #skF_2
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.06/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.06/1.24  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.24  
% 2.06/1.25  tff(f_67, negated_conjecture, ~(![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.06/1.25  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.06/1.25  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.06/1.25  tff(f_56, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.06/1.25  tff(c_24, plain, (~v1_xboole_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.25  tff(c_22, plain, (r1_tarski('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.25  tff(c_20, plain, (r1_tarski('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.25  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.25  tff(c_56, plain, (![C_33, B_34, A_35]: (r2_hidden(C_33, B_34) | ~r2_hidden(C_33, A_35) | ~r1_tarski(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.25  tff(c_68, plain, (![A_1, B_34]: (r2_hidden('#skF_1'(A_1), B_34) | ~r1_tarski(A_1, B_34) | v1_xboole_0(A_1))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.06/1.25  tff(c_118, plain, (![A_43, B_44]: (r2_hidden('#skF_1'(A_43), B_44) | ~r1_tarski(A_43, B_44) | v1_xboole_0(A_43))), inference(resolution, [status(thm)], [c_4, c_56])).
% 2.06/1.25  tff(c_18, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.06/1.25  tff(c_69, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.25  tff(c_78, plain, (![C_38]: (~r2_hidden(C_38, '#skF_5') | ~r2_hidden(C_38, '#skF_4'))), inference(resolution, [status(thm)], [c_18, c_69])).
% 2.06/1.25  tff(c_167, plain, (![A_49]: (~r2_hidden('#skF_1'(A_49), '#skF_4') | ~r1_tarski(A_49, '#skF_5') | v1_xboole_0(A_49))), inference(resolution, [status(thm)], [c_118, c_78])).
% 2.06/1.25  tff(c_251, plain, (![A_61]: (~r1_tarski(A_61, '#skF_5') | ~r1_tarski(A_61, '#skF_4') | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_68, c_167])).
% 2.06/1.25  tff(c_262, plain, (~r1_tarski('#skF_6', '#skF_4') | v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_20, c_251])).
% 2.06/1.25  tff(c_268, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_262])).
% 2.06/1.25  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_268])).
% 2.06/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.25  
% 2.06/1.25  Inference rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Ref     : 0
% 2.06/1.25  #Sup     : 53
% 2.06/1.25  #Fact    : 0
% 2.06/1.25  #Define  : 0
% 2.06/1.25  #Split   : 3
% 2.06/1.25  #Chain   : 0
% 2.06/1.25  #Close   : 0
% 2.06/1.25  
% 2.06/1.25  Ordering : KBO
% 2.06/1.25  
% 2.06/1.25  Simplification rules
% 2.06/1.25  ----------------------
% 2.06/1.25  #Subsume      : 16
% 2.06/1.25  #Demod        : 2
% 2.06/1.25  #Tautology    : 6
% 2.06/1.25  #SimpNegUnit  : 4
% 2.06/1.25  #BackRed      : 0
% 2.06/1.25  
% 2.06/1.25  #Partial instantiations: 0
% 2.06/1.25  #Strategies tried      : 1
% 2.06/1.25  
% 2.06/1.25  Timing (in seconds)
% 2.06/1.25  ----------------------
% 2.06/1.25  Preprocessing        : 0.26
% 2.06/1.25  Parsing              : 0.15
% 2.06/1.25  CNF conversion       : 0.02
% 2.06/1.25  Main loop            : 0.22
% 2.06/1.25  Inferencing          : 0.09
% 2.06/1.25  Reduction            : 0.05
% 2.06/1.25  Demodulation         : 0.03
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.26  Subsumption          : 0.05
% 2.06/1.26  Abstraction          : 0.01
% 2.06/1.26  MUC search           : 0.00
% 2.06/1.26  Cooper               : 0.00
% 2.06/1.26  Total                : 0.51
% 2.06/1.26  Index Insertion      : 0.00
% 2.06/1.26  Index Deletion       : 0.00
% 2.06/1.26  Index Matching       : 0.00
% 2.06/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
