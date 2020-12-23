%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:03 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   46 (  99 expanded)
%              Number of leaves         :   19 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   76 ( 240 expanded)
%              Number of equality atoms :   11 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_ordinal1,type,(
    v1_ordinal1: $i > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(v3_ordinal1,type,(
    v3_ordinal1: $i > $o )).

tff(v2_ordinal1,type,(
    v2_ordinal1: $i > $o )).

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_ordinal1(A)
       => ! [B] :
            ( v3_ordinal1(B)
           => ! [C] :
                ( v3_ordinal1(C)
               => ( ( r1_tarski(A,B)
                    & r2_hidden(B,C) )
                 => r2_hidden(A,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_ordinal1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v3_ordinal1(A)
     => ( v1_ordinal1(A)
        & v2_ordinal1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
    <=> ! [B] :
          ( r2_hidden(B,A)
         => r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_ordinal1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r2_xboole_0(A,B)
        & r1_tarski(B,C) )
     => r2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_xboole_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_ordinal1(A)
     => ! [B] :
          ( v3_ordinal1(B)
         => ( r2_xboole_0(A,B)
           => r2_hidden(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

tff(c_24,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r2_xboole_0(A_1,B_2)
      | B_2 = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v3_ordinal1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_43,plain,(
    ! [A_20] :
      ( v1_ordinal1(A_20)
      | ~ v3_ordinal1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_50,plain,(
    v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_66,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(B_27,A_28)
      | ~ r2_hidden(B_27,A_28)
      | ~ v1_ordinal1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,
    ( r1_tarski('#skF_3','#skF_4')
    | ~ v1_ordinal1('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_66])).

tff(c_76,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_72])).

tff(c_77,plain,(
    ! [A_29,C_30,B_31] :
      ( r2_xboole_0(A_29,C_30)
      | ~ r1_tarski(B_31,C_30)
      | ~ r2_xboole_0(A_29,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_90,plain,(
    ! [A_33] :
      ( r2_xboole_0(A_33,'#skF_4')
      | ~ r2_xboole_0(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_76,c_77])).

tff(c_122,plain,(
    ! [A_37] :
      ( r2_xboole_0(A_37,'#skF_4')
      | A_37 = '#skF_3'
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_2,c_90])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ r2_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_4')
      | A_40 = '#skF_3'
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_122,c_6])).

tff(c_161,plain,
    ( r1_tarski('#skF_2','#skF_4')
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_157])).

tff(c_162,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_161])).

tff(c_22,plain,(
    ~ r2_hidden('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_180,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_22])).

tff(c_185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_180])).

tff(c_187,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_161])).

tff(c_32,plain,(
    v1_ordinal1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    ! [A_11,B_13] :
      ( r2_hidden(A_11,B_13)
      | ~ r2_xboole_0(A_11,B_13)
      | ~ v3_ordinal1(B_13)
      | ~ v1_ordinal1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_125,plain,(
    ! [A_37] :
      ( r2_hidden(A_37,'#skF_4')
      | ~ v3_ordinal1('#skF_4')
      | ~ v1_ordinal1(A_37)
      | A_37 = '#skF_3'
      | ~ r1_tarski(A_37,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_122,c_20])).

tff(c_219,plain,(
    ! [A_47] :
      ( r2_hidden(A_47,'#skF_4')
      | ~ v1_ordinal1(A_47)
      | A_47 = '#skF_3'
      | ~ r1_tarski(A_47,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_125])).

tff(c_225,plain,
    ( ~ v1_ordinal1('#skF_2')
    | '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_219,c_22])).

tff(c_231,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_32,c_225])).

tff(c_233,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:15:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.31  
% 1.93/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.31  %$ r2_xboole_0 > r2_hidden > r1_tarski > v3_ordinal1 > v2_ordinal1 > v1_ordinal1 > #nlpp > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 1.93/1.31  
% 1.93/1.31  %Foreground sorts:
% 1.93/1.31  
% 1.93/1.31  
% 1.93/1.31  %Background operators:
% 1.93/1.31  
% 1.93/1.31  
% 1.93/1.31  %Foreground operators:
% 1.93/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.31  tff(v1_ordinal1, type, v1_ordinal1: $i > $o).
% 1.93/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.93/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.93/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.31  tff(v3_ordinal1, type, v3_ordinal1: $i > $o).
% 1.93/1.31  tff(v2_ordinal1, type, v2_ordinal1: $i > $o).
% 1.93/1.31  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 1.93/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.31  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.31  
% 2.21/1.32  tff(f_75, negated_conjecture, ~(![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (![C]: (v3_ordinal1(C) => ((r1_tarski(A, B) & r2_hidden(B, C)) => r2_hidden(A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_ordinal1)).
% 2.21/1.32  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.21/1.32  tff(f_44, axiom, (![A]: (v3_ordinal1(A) => (v1_ordinal1(A) & v2_ordinal1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_ordinal1)).
% 2.21/1.32  tff(f_51, axiom, (![A]: (v1_ordinal1(A) <=> (![B]: (r2_hidden(B, A) => r1_tarski(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_ordinal1)).
% 2.21/1.32  tff(f_38, axiom, (![A, B, C]: ((r2_xboole_0(A, B) & r1_tarski(B, C)) => r2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_xboole_1)).
% 2.21/1.32  tff(f_60, axiom, (![A]: (v1_ordinal1(A) => (![B]: (v3_ordinal1(B) => (r2_xboole_0(A, B) => r2_hidden(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_ordinal1)).
% 2.21/1.32  tff(c_24, plain, (r2_hidden('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.32  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.32  tff(c_2, plain, (![A_1, B_2]: (r2_xboole_0(A_1, B_2) | B_2=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.32  tff(c_28, plain, (v3_ordinal1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.32  tff(c_43, plain, (![A_20]: (v1_ordinal1(A_20) | ~v3_ordinal1(A_20))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.21/1.32  tff(c_50, plain, (v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_28, c_43])).
% 2.21/1.32  tff(c_66, plain, (![B_27, A_28]: (r1_tarski(B_27, A_28) | ~r2_hidden(B_27, A_28) | ~v1_ordinal1(A_28))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.32  tff(c_72, plain, (r1_tarski('#skF_3', '#skF_4') | ~v1_ordinal1('#skF_4')), inference(resolution, [status(thm)], [c_24, c_66])).
% 2.21/1.32  tff(c_76, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_72])).
% 2.21/1.32  tff(c_77, plain, (![A_29, C_30, B_31]: (r2_xboole_0(A_29, C_30) | ~r1_tarski(B_31, C_30) | ~r2_xboole_0(A_29, B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.21/1.32  tff(c_90, plain, (![A_33]: (r2_xboole_0(A_33, '#skF_4') | ~r2_xboole_0(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_76, c_77])).
% 2.21/1.32  tff(c_122, plain, (![A_37]: (r2_xboole_0(A_37, '#skF_4') | A_37='#skF_3' | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_2, c_90])).
% 2.21/1.32  tff(c_6, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~r2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.32  tff(c_157, plain, (![A_40]: (r1_tarski(A_40, '#skF_4') | A_40='#skF_3' | ~r1_tarski(A_40, '#skF_3'))), inference(resolution, [status(thm)], [c_122, c_6])).
% 2.21/1.32  tff(c_161, plain, (r1_tarski('#skF_2', '#skF_4') | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_26, c_157])).
% 2.21/1.32  tff(c_162, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_161])).
% 2.21/1.32  tff(c_22, plain, (~r2_hidden('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.32  tff(c_180, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_22])).
% 2.21/1.32  tff(c_185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_180])).
% 2.21/1.32  tff(c_187, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_161])).
% 2.21/1.32  tff(c_32, plain, (v1_ordinal1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.21/1.32  tff(c_20, plain, (![A_11, B_13]: (r2_hidden(A_11, B_13) | ~r2_xboole_0(A_11, B_13) | ~v3_ordinal1(B_13) | ~v1_ordinal1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.21/1.32  tff(c_125, plain, (![A_37]: (r2_hidden(A_37, '#skF_4') | ~v3_ordinal1('#skF_4') | ~v1_ordinal1(A_37) | A_37='#skF_3' | ~r1_tarski(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_122, c_20])).
% 2.21/1.32  tff(c_219, plain, (![A_47]: (r2_hidden(A_47, '#skF_4') | ~v1_ordinal1(A_47) | A_47='#skF_3' | ~r1_tarski(A_47, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_125])).
% 2.21/1.32  tff(c_225, plain, (~v1_ordinal1('#skF_2') | '#skF_2'='#skF_3' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_219, c_22])).
% 2.21/1.32  tff(c_231, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_32, c_225])).
% 2.21/1.32  tff(c_233, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_231])).
% 2.21/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.32  
% 2.21/1.32  Inference rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Ref     : 0
% 2.21/1.32  #Sup     : 33
% 2.21/1.32  #Fact    : 0
% 2.21/1.32  #Define  : 0
% 2.21/1.32  #Split   : 4
% 2.21/1.32  #Chain   : 0
% 2.21/1.32  #Close   : 0
% 2.21/1.32  
% 2.21/1.32  Ordering : KBO
% 2.21/1.32  
% 2.21/1.32  Simplification rules
% 2.21/1.32  ----------------------
% 2.21/1.32  #Subsume      : 7
% 2.21/1.32  #Demod        : 25
% 2.21/1.32  #Tautology    : 7
% 2.21/1.32  #SimpNegUnit  : 1
% 2.21/1.32  #BackRed      : 7
% 2.21/1.32  
% 2.21/1.32  #Partial instantiations: 0
% 2.21/1.32  #Strategies tried      : 1
% 2.21/1.32  
% 2.21/1.32  Timing (in seconds)
% 2.21/1.32  ----------------------
% 2.21/1.32  Preprocessing        : 0.27
% 2.21/1.32  Parsing              : 0.15
% 2.21/1.32  CNF conversion       : 0.02
% 2.21/1.32  Main loop            : 0.25
% 2.21/1.32  Inferencing          : 0.10
% 2.21/1.32  Reduction            : 0.06
% 2.21/1.32  Demodulation         : 0.04
% 2.21/1.33  BG Simplification    : 0.02
% 2.21/1.33  Subsumption          : 0.06
% 2.21/1.33  Abstraction          : 0.01
% 2.21/1.33  MUC search           : 0.00
% 2.21/1.33  Cooper               : 0.00
% 2.21/1.33  Total                : 0.55
% 2.21/1.33  Index Insertion      : 0.00
% 2.21/1.33  Index Deletion       : 0.00
% 2.21/1.33  Index Matching       : 0.00
% 2.21/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
