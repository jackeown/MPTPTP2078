%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 16.51s
% Output     : CNFRefutation 16.51s
% Verified   : 
% Statistics : Number of formulae       :   34 (  40 expanded)
%              Number of leaves         :   18 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
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

tff(c_36,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_79,plain,(
    ! [C_32,B_33,A_34] :
      ( r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r1_tarski(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    ! [A_1,B_2,B_33] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_33)
      | ~ r1_tarski(A_1,B_33)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_117,plain,(
    ! [D_41,A_42,B_43] :
      ( r2_hidden(D_41,k4_xboole_0(A_42,B_43))
      | r2_hidden(D_41,B_43)
      | ~ r2_hidden(D_41,A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2556,plain,(
    ! [A_311,A_312,B_313] :
      ( r1_tarski(A_311,k4_xboole_0(A_312,B_313))
      | r2_hidden('#skF_1'(A_311,k4_xboole_0(A_312,B_313)),B_313)
      | ~ r2_hidden('#skF_1'(A_311,k4_xboole_0(A_312,B_313)),A_312) ) ),
    inference(resolution,[status(thm)],[c_117,c_4])).

tff(c_28486,plain,(
    ! [A_948,B_949,B_950] :
      ( r2_hidden('#skF_1'(A_948,k4_xboole_0(B_949,B_950)),B_950)
      | ~ r1_tarski(A_948,B_949)
      | r1_tarski(A_948,k4_xboole_0(B_949,B_950)) ) ),
    inference(resolution,[status(thm)],[c_87,c_2556])).

tff(c_34,plain,(
    r1_xboole_0('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_89,plain,(
    ! [A_35,B_36,C_37] :
      ( ~ r1_xboole_0(A_35,B_36)
      | ~ r2_hidden(C_37,B_36)
      | ~ r2_hidden(C_37,A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92,plain,(
    ! [C_37] :
      ( ~ r2_hidden(C_37,'#skF_7')
      | ~ r2_hidden(C_37,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_34,c_89])).

tff(c_36995,plain,(
    ! [A_1061,B_1062] :
      ( ~ r2_hidden('#skF_1'(A_1061,k4_xboole_0(B_1062,'#skF_7')),'#skF_5')
      | ~ r1_tarski(A_1061,B_1062)
      | r1_tarski(A_1061,k4_xboole_0(B_1062,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_28486,c_92])).

tff(c_37070,plain,(
    ! [B_1063] :
      ( ~ r1_tarski('#skF_5',B_1063)
      | r1_tarski('#skF_5',k4_xboole_0(B_1063,'#skF_7')) ) ),
    inference(resolution,[status(thm)],[c_6,c_36995])).

tff(c_32,plain,(
    ~ r1_tarski('#skF_5',k4_xboole_0('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_37229,plain,(
    ~ r1_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_37070,c_32])).

tff(c_37357,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_37229])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.51/6.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/6.69  
% 16.51/6.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/6.69  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.51/6.69  
% 16.51/6.69  %Foreground sorts:
% 16.51/6.69  
% 16.51/6.69  
% 16.51/6.69  %Background operators:
% 16.51/6.69  
% 16.51/6.69  
% 16.51/6.69  %Foreground operators:
% 16.51/6.69  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.51/6.69  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.51/6.69  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 16.51/6.69  tff('#skF_7', type, '#skF_7': $i).
% 16.51/6.69  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.51/6.69  tff('#skF_5', type, '#skF_5': $i).
% 16.51/6.69  tff('#skF_6', type, '#skF_6': $i).
% 16.51/6.69  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 16.51/6.69  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 16.51/6.69  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.51/6.69  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 16.51/6.69  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.51/6.69  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 16.51/6.69  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 16.51/6.69  
% 16.51/6.70  tff(f_67, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 16.51/6.70  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 16.51/6.70  tff(f_42, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 16.51/6.70  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 16.51/6.70  tff(c_36, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.51/6.70  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.51/6.70  tff(c_79, plain, (![C_32, B_33, A_34]: (r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r1_tarski(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.51/6.70  tff(c_87, plain, (![A_1, B_2, B_33]: (r2_hidden('#skF_1'(A_1, B_2), B_33) | ~r1_tarski(A_1, B_33) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_79])).
% 16.51/6.70  tff(c_117, plain, (![D_41, A_42, B_43]: (r2_hidden(D_41, k4_xboole_0(A_42, B_43)) | r2_hidden(D_41, B_43) | ~r2_hidden(D_41, A_42))), inference(cnfTransformation, [status(thm)], [f_42])).
% 16.51/6.70  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 16.51/6.70  tff(c_2556, plain, (![A_311, A_312, B_313]: (r1_tarski(A_311, k4_xboole_0(A_312, B_313)) | r2_hidden('#skF_1'(A_311, k4_xboole_0(A_312, B_313)), B_313) | ~r2_hidden('#skF_1'(A_311, k4_xboole_0(A_312, B_313)), A_312))), inference(resolution, [status(thm)], [c_117, c_4])).
% 16.51/6.70  tff(c_28486, plain, (![A_948, B_949, B_950]: (r2_hidden('#skF_1'(A_948, k4_xboole_0(B_949, B_950)), B_950) | ~r1_tarski(A_948, B_949) | r1_tarski(A_948, k4_xboole_0(B_949, B_950)))), inference(resolution, [status(thm)], [c_87, c_2556])).
% 16.51/6.70  tff(c_34, plain, (r1_xboole_0('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.51/6.70  tff(c_89, plain, (![A_35, B_36, C_37]: (~r1_xboole_0(A_35, B_36) | ~r2_hidden(C_37, B_36) | ~r2_hidden(C_37, A_35))), inference(cnfTransformation, [status(thm)], [f_60])).
% 16.51/6.70  tff(c_92, plain, (![C_37]: (~r2_hidden(C_37, '#skF_7') | ~r2_hidden(C_37, '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_89])).
% 16.51/6.70  tff(c_36995, plain, (![A_1061, B_1062]: (~r2_hidden('#skF_1'(A_1061, k4_xboole_0(B_1062, '#skF_7')), '#skF_5') | ~r1_tarski(A_1061, B_1062) | r1_tarski(A_1061, k4_xboole_0(B_1062, '#skF_7')))), inference(resolution, [status(thm)], [c_28486, c_92])).
% 16.51/6.70  tff(c_37070, plain, (![B_1063]: (~r1_tarski('#skF_5', B_1063) | r1_tarski('#skF_5', k4_xboole_0(B_1063, '#skF_7')))), inference(resolution, [status(thm)], [c_6, c_36995])).
% 16.51/6.70  tff(c_32, plain, (~r1_tarski('#skF_5', k4_xboole_0('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.51/6.70  tff(c_37229, plain, (~r1_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_37070, c_32])).
% 16.51/6.70  tff(c_37357, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_37229])).
% 16.51/6.70  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 16.51/6.70  
% 16.51/6.70  Inference rules
% 16.51/6.70  ----------------------
% 16.51/6.70  #Ref     : 0
% 16.51/6.70  #Sup     : 9485
% 16.51/6.70  #Fact    : 0
% 16.51/6.70  #Define  : 0
% 16.51/6.70  #Split   : 5
% 16.51/6.70  #Chain   : 0
% 16.51/6.70  #Close   : 0
% 16.51/6.70  
% 16.51/6.70  Ordering : KBO
% 16.51/6.70  
% 16.51/6.70  Simplification rules
% 16.51/6.70  ----------------------
% 16.51/6.70  #Subsume      : 3243
% 16.51/6.70  #Demod        : 4989
% 16.51/6.70  #Tautology    : 2918
% 16.51/6.70  #SimpNegUnit  : 42
% 16.51/6.70  #BackRed      : 18
% 16.51/6.70  
% 16.51/6.70  #Partial instantiations: 0
% 16.51/6.70  #Strategies tried      : 1
% 16.51/6.70  
% 16.51/6.70  Timing (in seconds)
% 16.51/6.70  ----------------------
% 16.51/6.70  Preprocessing        : 0.29
% 16.51/6.70  Parsing              : 0.15
% 16.51/6.70  CNF conversion       : 0.02
% 16.51/6.70  Main loop            : 5.65
% 16.51/6.70  Inferencing          : 1.09
% 16.51/6.70  Reduction            : 1.96
% 16.51/6.70  Demodulation         : 1.51
% 16.51/6.70  BG Simplification    : 0.11
% 16.51/6.70  Subsumption          : 2.15
% 16.51/6.70  Abstraction          : 0.17
% 16.51/6.70  MUC search           : 0.00
% 16.51/6.70  Cooper               : 0.00
% 16.51/6.70  Total                : 5.97
% 16.51/6.70  Index Insertion      : 0.00
% 16.51/6.70  Index Deletion       : 0.00
% 16.51/6.70  Index Matching       : 0.00
% 16.51/6.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
