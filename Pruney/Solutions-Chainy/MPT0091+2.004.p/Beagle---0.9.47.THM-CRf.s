%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:28 EST 2020

% Result     : Theorem 3.85s
% Output     : CNFRefutation 3.85s
% Verified   : 
% Statistics : Number of formulae       :   33 (  46 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 ( 101 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_53,axiom,(
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

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_30,plain,(
    ~ r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),A_7)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_3'(A_7,B_8),B_8)
      | r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_100,plain,(
    ! [D_29,A_30,B_31] :
      ( r2_hidden(D_29,k4_xboole_0(A_30,B_31))
      | r2_hidden(D_29,B_31)
      | ~ r2_hidden(D_29,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_26,plain,(
    r1_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_55,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r1_xboole_0(A_22,B_23)
      | ~ r2_hidden(C_24,B_23)
      | ~ r2_hidden(C_24,A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,k4_xboole_0('#skF_5','#skF_6'))
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_55])).

tff(c_114,plain,(
    ! [D_32] :
      ( ~ r2_hidden(D_32,'#skF_4')
      | r2_hidden(D_32,'#skF_6')
      | ~ r2_hidden(D_32,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_100,c_60])).

tff(c_1912,plain,(
    ! [B_167] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_167),'#skF_4')
      | r2_hidden('#skF_3'('#skF_5',B_167),'#skF_6')
      | r1_xboole_0('#skF_5',B_167) ) ),
    inference(resolution,[status(thm)],[c_24,c_114])).

tff(c_28,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_61,plain,(
    ! [C_24] :
      ( ~ r2_hidden(C_24,'#skF_6')
      | ~ r2_hidden(C_24,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_55])).

tff(c_1932,plain,(
    ! [B_168] :
      ( ~ r2_hidden('#skF_3'('#skF_5',B_168),'#skF_4')
      | r1_xboole_0('#skF_5',B_168) ) ),
    inference(resolution,[status(thm)],[c_1912,c_61])).

tff(c_1942,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_1932])).

tff(c_20,plain,(
    ! [A_7,B_8,C_11] :
      ( ~ r1_xboole_0(A_7,B_8)
      | ~ r2_hidden(C_11,B_8)
      | ~ r2_hidden(C_11,A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1958,plain,(
    ! [C_170] :
      ( ~ r2_hidden(C_170,'#skF_4')
      | ~ r2_hidden(C_170,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_1942,c_20])).

tff(c_2118,plain,(
    ! [A_177] :
      ( ~ r2_hidden('#skF_3'(A_177,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_177,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_22,c_1958])).

tff(c_2126,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_2118])).

tff(c_2131,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_2126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:18:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.85/1.66  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.66  
% 3.85/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 3.85/1.67  
% 3.85/1.67  %Foreground sorts:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Background operators:
% 3.85/1.67  
% 3.85/1.67  
% 3.85/1.67  %Foreground operators:
% 3.85/1.67  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.85/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.85/1.67  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.85/1.67  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.85/1.67  tff('#skF_5', type, '#skF_5': $i).
% 3.85/1.67  tff('#skF_6', type, '#skF_6': $i).
% 3.85/1.67  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.85/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.85/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.85/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.85/1.67  
% 3.85/1.67  tff(f_62, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_xboole_1)).
% 3.85/1.67  tff(f_53, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.85/1.67  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.85/1.67  tff(c_30, plain, (~r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.67  tff(c_24, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), A_7) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_22, plain, (![A_7, B_8]: (r2_hidden('#skF_3'(A_7, B_8), B_8) | r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_100, plain, (![D_29, A_30, B_31]: (r2_hidden(D_29, k4_xboole_0(A_30, B_31)) | r2_hidden(D_29, B_31) | ~r2_hidden(D_29, A_30))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.85/1.67  tff(c_26, plain, (r1_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.67  tff(c_55, plain, (![A_22, B_23, C_24]: (~r1_xboole_0(A_22, B_23) | ~r2_hidden(C_24, B_23) | ~r2_hidden(C_24, A_22))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_60, plain, (![C_24]: (~r2_hidden(C_24, k4_xboole_0('#skF_5', '#skF_6')) | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_26, c_55])).
% 3.85/1.67  tff(c_114, plain, (![D_32]: (~r2_hidden(D_32, '#skF_4') | r2_hidden(D_32, '#skF_6') | ~r2_hidden(D_32, '#skF_5'))), inference(resolution, [status(thm)], [c_100, c_60])).
% 3.85/1.67  tff(c_1912, plain, (![B_167]: (~r2_hidden('#skF_3'('#skF_5', B_167), '#skF_4') | r2_hidden('#skF_3'('#skF_5', B_167), '#skF_6') | r1_xboole_0('#skF_5', B_167))), inference(resolution, [status(thm)], [c_24, c_114])).
% 3.85/1.67  tff(c_28, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.85/1.67  tff(c_61, plain, (![C_24]: (~r2_hidden(C_24, '#skF_6') | ~r2_hidden(C_24, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_55])).
% 3.85/1.67  tff(c_1932, plain, (![B_168]: (~r2_hidden('#skF_3'('#skF_5', B_168), '#skF_4') | r1_xboole_0('#skF_5', B_168))), inference(resolution, [status(thm)], [c_1912, c_61])).
% 3.85/1.67  tff(c_1942, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_1932])).
% 3.85/1.67  tff(c_20, plain, (![A_7, B_8, C_11]: (~r1_xboole_0(A_7, B_8) | ~r2_hidden(C_11, B_8) | ~r2_hidden(C_11, A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.85/1.67  tff(c_1958, plain, (![C_170]: (~r2_hidden(C_170, '#skF_4') | ~r2_hidden(C_170, '#skF_5'))), inference(resolution, [status(thm)], [c_1942, c_20])).
% 3.85/1.67  tff(c_2118, plain, (![A_177]: (~r2_hidden('#skF_3'(A_177, '#skF_5'), '#skF_4') | r1_xboole_0(A_177, '#skF_5'))), inference(resolution, [status(thm)], [c_22, c_1958])).
% 3.85/1.67  tff(c_2126, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_24, c_2118])).
% 3.85/1.67  tff(c_2131, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_2126])).
% 3.85/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.85/1.67  
% 3.85/1.67  Inference rules
% 3.85/1.67  ----------------------
% 3.85/1.67  #Ref     : 0
% 3.85/1.67  #Sup     : 466
% 3.85/1.67  #Fact    : 0
% 3.85/1.67  #Define  : 0
% 3.85/1.67  #Split   : 0
% 3.85/1.67  #Chain   : 0
% 3.85/1.67  #Close   : 0
% 3.85/1.67  
% 3.85/1.67  Ordering : KBO
% 3.85/1.67  
% 3.85/1.67  Simplification rules
% 3.85/1.67  ----------------------
% 3.85/1.67  #Subsume      : 91
% 3.85/1.67  #Demod        : 147
% 3.85/1.67  #Tautology    : 107
% 3.85/1.67  #SimpNegUnit  : 1
% 3.85/1.67  #BackRed      : 3
% 3.85/1.67  
% 3.85/1.67  #Partial instantiations: 0
% 3.85/1.67  #Strategies tried      : 1
% 3.85/1.67  
% 3.85/1.67  Timing (in seconds)
% 3.85/1.67  ----------------------
% 3.85/1.68  Preprocessing        : 0.27
% 3.85/1.68  Parsing              : 0.15
% 3.85/1.68  CNF conversion       : 0.02
% 3.85/1.68  Main loop            : 0.65
% 3.85/1.68  Inferencing          : 0.23
% 3.85/1.68  Reduction            : 0.17
% 3.85/1.68  Demodulation         : 0.12
% 3.85/1.68  BG Simplification    : 0.03
% 3.85/1.68  Subsumption          : 0.17
% 3.85/1.68  Abstraction          : 0.03
% 3.85/1.68  MUC search           : 0.00
% 3.85/1.68  Cooper               : 0.00
% 3.85/1.68  Total                : 0.95
% 3.85/1.68  Index Insertion      : 0.00
% 3.85/1.68  Index Deletion       : 0.00
% 3.85/1.68  Index Matching       : 0.00
% 3.85/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
