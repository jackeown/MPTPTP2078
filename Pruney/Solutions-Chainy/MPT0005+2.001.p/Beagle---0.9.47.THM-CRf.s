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
% DateTime   : Thu Dec  3 09:42:27 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  82 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(A,B)
          & r2_hidden(C,k2_xboole_0(A,B))
          & ~ ( r2_hidden(C,A)
              & ~ r2_hidden(C,B) )
          & ~ ( r2_hidden(C,B)
              & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_52,axiom,(
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

tff(c_26,plain,
    ( r2_hidden('#skF_6','#skF_4')
    | ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_33,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_28,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | ~ r2_hidden('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_34,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_28])).

tff(c_30,plain,(
    r2_hidden('#skF_6',k2_xboole_0('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_70,plain,(
    ! [D_28,B_29,A_30] :
      ( r2_hidden(D_28,B_29)
      | r2_hidden(D_28,A_30)
      | ~ r2_hidden(D_28,k2_xboole_0(A_30,B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_87,plain,
    ( r2_hidden('#skF_6','#skF_5')
    | r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_70])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_33,c_87])).

tff(c_96,plain,(
    r2_hidden('#skF_6','#skF_4') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_97,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_32,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_104,plain,(
    ! [A_41,B_42,C_43] :
      ( ~ r1_xboole_0(A_41,B_42)
      | ~ r2_hidden(C_43,B_42)
      | ~ r2_hidden(C_43,A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_108,plain,(
    ! [C_44] :
      ( ~ r2_hidden(C_44,'#skF_5')
      | ~ r2_hidden(C_44,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_119,plain,(
    ~ r2_hidden('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_97,c_108])).

tff(c_125,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_96,c_119])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:54:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  
% 1.64/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.64/1.14  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 1.64/1.14  
% 1.64/1.14  %Foreground sorts:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Background operators:
% 1.64/1.14  
% 1.64/1.14  
% 1.64/1.14  %Foreground operators:
% 1.64/1.14  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.14  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.64/1.14  tff('#skF_5', type, '#skF_5': $i).
% 1.64/1.14  tff('#skF_6', type, '#skF_6': $i).
% 1.64/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.14  tff('#skF_4', type, '#skF_4': $i).
% 1.64/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.14  
% 1.81/1.15  tff(f_70, negated_conjecture, ~(![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.81/1.15  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.81/1.15  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.81/1.15  tff(c_26, plain, (r2_hidden('#skF_6', '#skF_4') | ~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.81/1.15  tff(c_33, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(splitLeft, [status(thm)], [c_26])).
% 1.81/1.15  tff(c_28, plain, (r2_hidden('#skF_6', '#skF_5') | ~r2_hidden('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.81/1.15  tff(c_34, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_33, c_28])).
% 1.81/1.15  tff(c_30, plain, (r2_hidden('#skF_6', k2_xboole_0('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.81/1.15  tff(c_70, plain, (![D_28, B_29, A_30]: (r2_hidden(D_28, B_29) | r2_hidden(D_28, A_30) | ~r2_hidden(D_28, k2_xboole_0(A_30, B_29)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.81/1.15  tff(c_87, plain, (r2_hidden('#skF_6', '#skF_5') | r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_70])).
% 1.81/1.15  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_33, c_87])).
% 1.81/1.15  tff(c_96, plain, (r2_hidden('#skF_6', '#skF_4')), inference(splitRight, [status(thm)], [c_26])).
% 1.81/1.15  tff(c_97, plain, (r2_hidden('#skF_6', '#skF_5')), inference(splitRight, [status(thm)], [c_26])).
% 1.81/1.15  tff(c_32, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.81/1.15  tff(c_104, plain, (![A_41, B_42, C_43]: (~r1_xboole_0(A_41, B_42) | ~r2_hidden(C_43, B_42) | ~r2_hidden(C_43, A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.15  tff(c_108, plain, (![C_44]: (~r2_hidden(C_44, '#skF_5') | ~r2_hidden(C_44, '#skF_4'))), inference(resolution, [status(thm)], [c_32, c_104])).
% 1.81/1.15  tff(c_119, plain, (~r2_hidden('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_97, c_108])).
% 1.81/1.15  tff(c_125, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_96, c_119])).
% 1.81/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.81/1.15  
% 1.81/1.15  Inference rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Ref     : 0
% 1.81/1.15  #Sup     : 15
% 1.81/1.15  #Fact    : 0
% 1.81/1.15  #Define  : 0
% 1.81/1.15  #Split   : 1
% 1.81/1.15  #Chain   : 0
% 1.81/1.15  #Close   : 0
% 1.81/1.15  
% 1.81/1.15  Ordering : KBO
% 1.81/1.15  
% 1.81/1.15  Simplification rules
% 1.81/1.15  ----------------------
% 1.81/1.15  #Subsume      : 1
% 1.81/1.15  #Demod        : 4
% 1.81/1.15  #Tautology    : 4
% 1.81/1.15  #SimpNegUnit  : 2
% 1.81/1.15  #BackRed      : 0
% 1.81/1.15  
% 1.81/1.15  #Partial instantiations: 0
% 1.81/1.15  #Strategies tried      : 1
% 1.81/1.15  
% 1.81/1.15  Timing (in seconds)
% 1.81/1.15  ----------------------
% 1.81/1.15  Preprocessing        : 0.26
% 1.81/1.15  Parsing              : 0.14
% 1.81/1.15  CNF conversion       : 0.02
% 1.81/1.15  Main loop            : 0.14
% 1.81/1.15  Inferencing          : 0.06
% 1.81/1.15  Reduction            : 0.03
% 1.81/1.15  Demodulation         : 0.02
% 1.81/1.15  BG Simplification    : 0.01
% 1.81/1.15  Subsumption          : 0.03
% 1.81/1.15  Abstraction          : 0.01
% 1.81/1.15  MUC search           : 0.00
% 1.81/1.15  Cooper               : 0.00
% 1.81/1.15  Total                : 0.42
% 1.81/1.15  Index Insertion      : 0.00
% 1.81/1.15  Index Deletion       : 0.00
% 1.81/1.15  Index Matching       : 0.00
% 1.81/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
