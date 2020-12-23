%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:48 EST 2020

% Result     : Theorem 4.01s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    8
%              Number of atoms          :   63 (  93 expanded)
%              Number of equality atoms :   12 (  15 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_28,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),B_12)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_11,B_12] :
      ( r2_hidden('#skF_3'(A_11,B_12),A_11)
      | r1_xboole_0(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_310,plain,(
    ! [D_78,A_79,B_80] :
      ( ~ r2_hidden(D_78,'#skF_4'(A_79,B_80))
      | ~ r2_hidden(D_78,B_80)
      | ~ r2_hidden(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3002,plain,(
    ! [A_217,B_218,B_219] :
      ( ~ r2_hidden('#skF_3'('#skF_4'(A_217,B_218),B_219),B_218)
      | ~ r2_hidden(A_217,B_218)
      | r1_xboole_0('#skF_4'(A_217,B_218),B_219) ) ),
    inference(resolution,[status(thm)],[c_30,c_310])).

tff(c_3023,plain,(
    ! [A_220,B_221] :
      ( ~ r2_hidden(A_220,B_221)
      | r1_xboole_0('#skF_4'(A_220,B_221),B_221) ) ),
    inference(resolution,[status(thm)],[c_28,c_3002])).

tff(c_156,plain,(
    ! [A_51,B_52] :
      ( r2_hidden('#skF_4'(A_51,B_52),B_52)
      | ~ r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_25] :
      ( ~ r1_xboole_0(B_25,'#skF_5')
      | ~ r2_hidden(B_25,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,(
    ! [A_51] :
      ( ~ r1_xboole_0('#skF_4'(A_51,'#skF_5'),'#skF_5')
      | ~ r2_hidden(A_51,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_156,c_38])).

tff(c_3039,plain,(
    ! [A_222] : ~ r2_hidden(A_222,'#skF_5') ),
    inference(resolution,[status(thm)],[c_3023,c_175])).

tff(c_3112,plain,(
    ! [A_11] : r1_xboole_0(A_11,'#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_3039])).

tff(c_595,plain,(
    ! [A_106,B_107,C_108] :
      ( r2_hidden('#skF_1'(A_106,B_107,C_108),B_107)
      | r2_hidden('#skF_2'(A_106,B_107,C_108),C_108)
      | k3_xboole_0(A_106,B_107) = C_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k3_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_662,plain,(
    ! [A_109,B_110] :
      ( r2_hidden('#skF_2'(A_109,B_110,B_110),B_110)
      | k3_xboole_0(A_109,B_110) = B_110 ) ),
    inference(resolution,[status(thm)],[c_595,c_14])).

tff(c_698,plain,(
    ! [A_109] :
      ( ~ r1_xboole_0('#skF_2'(A_109,'#skF_5','#skF_5'),'#skF_5')
      | k3_xboole_0(A_109,'#skF_5') = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_662,c_38])).

tff(c_3277,plain,(
    ! [A_228] : k3_xboole_0(A_228,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3112,c_698])).

tff(c_32,plain,(
    ! [A_16] : r1_xboole_0(A_16,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [B_27,A_28] :
      ( r1_xboole_0(B_27,A_28)
      | ~ r1_xboole_0(A_28,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_45,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_56,plain,(
    ! [A_33,B_34] :
      ( k3_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_xboole_0(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,(
    ! [A_16] : k3_xboole_0(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_45,c_56])).

tff(c_3392,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_3277,c_67])).

tff(c_3454,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_3392])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 09:25:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.01/1.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.72  
% 4.01/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.73  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 4.01/1.73  
% 4.01/1.73  %Foreground sorts:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Background operators:
% 4.01/1.73  
% 4.01/1.73  
% 4.01/1.73  %Foreground operators:
% 4.01/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.01/1.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.01/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.01/1.73  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.01/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.01/1.73  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.01/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.01/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.01/1.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.01/1.73  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.01/1.73  
% 4.01/1.74  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 4.01/1.74  tff(f_60, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.01/1.74  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.01/1.74  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 4.01/1.74  tff(f_62, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.01/1.74  tff(f_42, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.01/1.74  tff(f_38, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 4.01/1.74  tff(c_40, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.01/1.74  tff(c_28, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), B_12) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.01/1.74  tff(c_30, plain, (![A_11, B_12]: (r2_hidden('#skF_3'(A_11, B_12), A_11) | r1_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.01/1.74  tff(c_310, plain, (![D_78, A_79, B_80]: (~r2_hidden(D_78, '#skF_4'(A_79, B_80)) | ~r2_hidden(D_78, B_80) | ~r2_hidden(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.74  tff(c_3002, plain, (![A_217, B_218, B_219]: (~r2_hidden('#skF_3'('#skF_4'(A_217, B_218), B_219), B_218) | ~r2_hidden(A_217, B_218) | r1_xboole_0('#skF_4'(A_217, B_218), B_219))), inference(resolution, [status(thm)], [c_30, c_310])).
% 4.01/1.74  tff(c_3023, plain, (![A_220, B_221]: (~r2_hidden(A_220, B_221) | r1_xboole_0('#skF_4'(A_220, B_221), B_221))), inference(resolution, [status(thm)], [c_28, c_3002])).
% 4.01/1.74  tff(c_156, plain, (![A_51, B_52]: (r2_hidden('#skF_4'(A_51, B_52), B_52) | ~r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.74  tff(c_38, plain, (![B_25]: (~r1_xboole_0(B_25, '#skF_5') | ~r2_hidden(B_25, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.01/1.74  tff(c_175, plain, (![A_51]: (~r1_xboole_0('#skF_4'(A_51, '#skF_5'), '#skF_5') | ~r2_hidden(A_51, '#skF_5'))), inference(resolution, [status(thm)], [c_156, c_38])).
% 4.01/1.74  tff(c_3039, plain, (![A_222]: (~r2_hidden(A_222, '#skF_5'))), inference(resolution, [status(thm)], [c_3023, c_175])).
% 4.01/1.74  tff(c_3112, plain, (![A_11]: (r1_xboole_0(A_11, '#skF_5'))), inference(resolution, [status(thm)], [c_28, c_3039])).
% 4.01/1.74  tff(c_595, plain, (![A_106, B_107, C_108]: (r2_hidden('#skF_1'(A_106, B_107, C_108), B_107) | r2_hidden('#skF_2'(A_106, B_107, C_108), C_108) | k3_xboole_0(A_106, B_107)=C_108)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.01/1.74  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k3_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.01/1.74  tff(c_662, plain, (![A_109, B_110]: (r2_hidden('#skF_2'(A_109, B_110, B_110), B_110) | k3_xboole_0(A_109, B_110)=B_110)), inference(resolution, [status(thm)], [c_595, c_14])).
% 4.01/1.74  tff(c_698, plain, (![A_109]: (~r1_xboole_0('#skF_2'(A_109, '#skF_5', '#skF_5'), '#skF_5') | k3_xboole_0(A_109, '#skF_5')='#skF_5')), inference(resolution, [status(thm)], [c_662, c_38])).
% 4.01/1.74  tff(c_3277, plain, (![A_228]: (k3_xboole_0(A_228, '#skF_5')='#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3112, c_698])).
% 4.01/1.74  tff(c_32, plain, (![A_16]: (r1_xboole_0(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.01/1.74  tff(c_42, plain, (![B_27, A_28]: (r1_xboole_0(B_27, A_28) | ~r1_xboole_0(A_28, B_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.01/1.74  tff(c_45, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(resolution, [status(thm)], [c_32, c_42])).
% 4.01/1.74  tff(c_56, plain, (![A_33, B_34]: (k3_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.01/1.74  tff(c_67, plain, (![A_16]: (k3_xboole_0(k1_xboole_0, A_16)=k1_xboole_0)), inference(resolution, [status(thm)], [c_45, c_56])).
% 4.01/1.74  tff(c_3392, plain, (k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_3277, c_67])).
% 4.01/1.74  tff(c_3454, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_3392])).
% 4.01/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.74  
% 4.01/1.74  Inference rules
% 4.01/1.74  ----------------------
% 4.01/1.74  #Ref     : 0
% 4.01/1.74  #Sup     : 800
% 4.01/1.74  #Fact    : 0
% 4.01/1.74  #Define  : 0
% 4.01/1.74  #Split   : 0
% 4.01/1.74  #Chain   : 0
% 4.01/1.74  #Close   : 0
% 4.01/1.74  
% 4.01/1.74  Ordering : KBO
% 4.01/1.74  
% 4.01/1.74  Simplification rules
% 4.01/1.74  ----------------------
% 4.01/1.74  #Subsume      : 104
% 4.01/1.74  #Demod        : 460
% 4.01/1.74  #Tautology    : 379
% 4.01/1.74  #SimpNegUnit  : 14
% 4.01/1.74  #BackRed      : 10
% 4.01/1.74  
% 4.01/1.74  #Partial instantiations: 0
% 4.01/1.74  #Strategies tried      : 1
% 4.01/1.74  
% 4.01/1.74  Timing (in seconds)
% 4.01/1.74  ----------------------
% 4.01/1.74  Preprocessing        : 0.28
% 4.01/1.74  Parsing              : 0.15
% 4.01/1.74  CNF conversion       : 0.02
% 4.01/1.74  Main loop            : 0.68
% 4.01/1.74  Inferencing          : 0.24
% 4.01/1.74  Reduction            : 0.18
% 4.01/1.74  Demodulation         : 0.13
% 4.01/1.74  BG Simplification    : 0.03
% 4.01/1.74  Subsumption          : 0.19
% 4.01/1.74  Abstraction          : 0.03
% 4.01/1.74  MUC search           : 0.00
% 4.01/1.74  Cooper               : 0.00
% 4.01/1.74  Total                : 0.99
% 4.01/1.74  Index Insertion      : 0.00
% 4.01/1.74  Index Deletion       : 0.00
% 4.01/1.74  Index Matching       : 0.00
% 4.01/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
