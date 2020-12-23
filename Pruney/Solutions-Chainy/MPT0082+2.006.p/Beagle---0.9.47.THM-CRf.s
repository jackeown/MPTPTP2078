%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:00 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  52 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_54,plain,(
    ~ r1_xboole_0('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_75,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_5'(A_40,B_41),k3_xboole_0(A_40,B_41))
      | r1_xboole_0(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [D_12,B_8,A_7] :
      ( r2_hidden(D_12,B_8)
      | ~ r2_hidden(D_12,k3_xboole_0(A_7,B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_86,plain,(
    ! [A_40,B_41] :
      ( r2_hidden('#skF_5'(A_40,B_41),B_41)
      | r1_xboole_0(A_40,B_41) ) ),
    inference(resolution,[status(thm)],[c_75,c_22])).

tff(c_38,plain,(
    ! [A_13,B_14] :
      ( r2_hidden('#skF_5'(A_13,B_14),k3_xboole_0(A_13,B_14))
      | r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,(
    r1_xboole_0(k3_xboole_0('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_153,plain,(
    ! [D_57,A_58,B_59] :
      ( r2_hidden(D_57,k3_xboole_0(A_58,B_59))
      | ~ r2_hidden(D_57,B_59)
      | ~ r2_hidden(D_57,A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_40,plain,(
    ! [A_13,B_14,C_17] :
      ( ~ r1_xboole_0(A_13,B_14)
      | ~ r2_hidden(C_17,k3_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_166,plain,(
    ! [A_60,B_61,D_62] :
      ( ~ r1_xboole_0(A_60,B_61)
      | ~ r2_hidden(D_62,B_61)
      | ~ r2_hidden(D_62,A_60) ) ),
    inference(resolution,[status(thm)],[c_153,c_40])).

tff(c_176,plain,(
    ! [D_63] :
      ( ~ r2_hidden(D_63,'#skF_7')
      | ~ r2_hidden(D_63,k3_xboole_0('#skF_6','#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_52,c_166])).

tff(c_192,plain,
    ( ~ r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_7')
    | r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_38,c_176])).

tff(c_198,plain,(
    ~ r2_hidden('#skF_5'('#skF_6','#skF_7'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_192])).

tff(c_201,plain,(
    r1_xboole_0('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_86,c_198])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:38:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.14  
% 1.80/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5
% 1.80/1.15  
% 1.80/1.15  %Foreground sorts:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Background operators:
% 1.80/1.15  
% 1.80/1.15  
% 1.80/1.15  %Foreground operators:
% 1.80/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.80/1.15  tff('#skF_7', type, '#skF_7': $i).
% 1.80/1.15  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.80/1.15  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.15  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.80/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.80/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.80/1.15  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.80/1.15  
% 1.80/1.15  tff(f_83, negated_conjecture, ~(![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.80/1.15  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.80/1.15  tff(f_43, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.80/1.15  tff(c_54, plain, (~r1_xboole_0('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.80/1.15  tff(c_75, plain, (![A_40, B_41]: (r2_hidden('#skF_5'(A_40, B_41), k3_xboole_0(A_40, B_41)) | r1_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.15  tff(c_22, plain, (![D_12, B_8, A_7]: (r2_hidden(D_12, B_8) | ~r2_hidden(D_12, k3_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.15  tff(c_86, plain, (![A_40, B_41]: (r2_hidden('#skF_5'(A_40, B_41), B_41) | r1_xboole_0(A_40, B_41))), inference(resolution, [status(thm)], [c_75, c_22])).
% 1.80/1.15  tff(c_38, plain, (![A_13, B_14]: (r2_hidden('#skF_5'(A_13, B_14), k3_xboole_0(A_13, B_14)) | r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.15  tff(c_52, plain, (r1_xboole_0(k3_xboole_0('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_83])).
% 1.80/1.15  tff(c_153, plain, (![D_57, A_58, B_59]: (r2_hidden(D_57, k3_xboole_0(A_58, B_59)) | ~r2_hidden(D_57, B_59) | ~r2_hidden(D_57, A_58))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.80/1.15  tff(c_40, plain, (![A_13, B_14, C_17]: (~r1_xboole_0(A_13, B_14) | ~r2_hidden(C_17, k3_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.15  tff(c_166, plain, (![A_60, B_61, D_62]: (~r1_xboole_0(A_60, B_61) | ~r2_hidden(D_62, B_61) | ~r2_hidden(D_62, A_60))), inference(resolution, [status(thm)], [c_153, c_40])).
% 1.80/1.15  tff(c_176, plain, (![D_63]: (~r2_hidden(D_63, '#skF_7') | ~r2_hidden(D_63, k3_xboole_0('#skF_6', '#skF_7')))), inference(resolution, [status(thm)], [c_52, c_166])).
% 1.80/1.15  tff(c_192, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_7') | r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_38, c_176])).
% 1.80/1.15  tff(c_198, plain, (~r2_hidden('#skF_5'('#skF_6', '#skF_7'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_54, c_192])).
% 1.80/1.15  tff(c_201, plain, (r1_xboole_0('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_86, c_198])).
% 1.80/1.15  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_201])).
% 1.80/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.15  
% 1.80/1.15  Inference rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Ref     : 0
% 1.80/1.15  #Sup     : 31
% 1.80/1.15  #Fact    : 0
% 1.80/1.15  #Define  : 0
% 1.80/1.15  #Split   : 0
% 1.80/1.15  #Chain   : 0
% 1.80/1.15  #Close   : 0
% 1.80/1.15  
% 1.80/1.15  Ordering : KBO
% 1.80/1.15  
% 1.80/1.15  Simplification rules
% 1.80/1.15  ----------------------
% 1.80/1.15  #Subsume      : 2
% 1.80/1.15  #Demod        : 0
% 1.80/1.15  #Tautology    : 11
% 1.80/1.15  #SimpNegUnit  : 2
% 1.80/1.15  #BackRed      : 0
% 1.80/1.15  
% 1.80/1.15  #Partial instantiations: 0
% 1.80/1.15  #Strategies tried      : 1
% 1.80/1.15  
% 1.80/1.15  Timing (in seconds)
% 1.80/1.15  ----------------------
% 1.80/1.16  Preprocessing        : 0.29
% 1.80/1.16  Parsing              : 0.16
% 1.80/1.16  CNF conversion       : 0.02
% 1.80/1.16  Main loop            : 0.17
% 1.80/1.16  Inferencing          : 0.06
% 1.80/1.16  Reduction            : 0.04
% 1.80/1.16  Demodulation         : 0.03
% 1.80/1.16  BG Simplification    : 0.02
% 1.80/1.16  Subsumption          : 0.04
% 1.80/1.16  Abstraction          : 0.01
% 1.80/1.16  MUC search           : 0.00
% 1.80/1.16  Cooper               : 0.00
% 1.80/1.16  Total                : 0.49
% 1.80/1.16  Index Insertion      : 0.00
% 1.80/1.16  Index Deletion       : 0.00
% 1.80/1.16  Index Matching       : 0.00
% 1.80/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
