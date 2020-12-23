%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 1.94s
% Verified   : 
% Statistics : Number of formulae       :   45 (  76 expanded)
%              Number of leaves         :   16 (  31 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 ( 136 expanded)
%              Number of equality atoms :   17 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_59,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_57,axiom,(
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

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_30,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26])).

tff(c_16,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_31,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_16])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_56,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_22])).

tff(c_79,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r2_hidden(C_34,B_33)
      | ~ r2_hidden(C_34,A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_95,plain,(
    ! [C_35] : ~ r2_hidden(C_35,'#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_79])).

tff(c_110,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_95])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_29,plain,(
    ! [A_5] :
      ( A_5 = '#skF_4'
      | ~ v1_xboole_0(A_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_113,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_29])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_113])).

tff(c_118,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_158,plain,(
    ! [A_50,B_51,C_52] :
      ( ~ r1_xboole_0(A_50,B_51)
      | ~ r2_hidden(C_52,B_51)
      | ~ r2_hidden(C_52,A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_174,plain,(
    ! [C_53] : ~ r2_hidden(C_53,'#skF_3') ),
    inference(resolution,[status(thm)],[c_118,c_158])).

tff(c_189,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_192,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_189,c_6])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_192])).

tff(c_197,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_199,plain,(
    ! [A_13] : r1_xboole_0(A_13,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_16])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_204,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_198])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_204,c_197,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:14:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.24  
% 1.94/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.25  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.94/1.25  
% 1.94/1.25  %Foreground sorts:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Background operators:
% 1.94/1.25  
% 1.94/1.25  
% 1.94/1.25  %Foreground operators:
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.94/1.25  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.94/1.25  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.94/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.94/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.94/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.25  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.94/1.25  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.94/1.25  
% 1.94/1.26  tff(f_72, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.94/1.26  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.94/1.26  tff(f_59, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.94/1.26  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.94/1.26  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.94/1.26  tff(c_20, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.26  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 1.94/1.26  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.94/1.26  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.26  tff(c_28, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 1.94/1.26  tff(c_30, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_26])).
% 1.94/1.26  tff(c_16, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.94/1.26  tff(c_31, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_16])).
% 1.94/1.26  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.26  tff(c_56, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_31, c_22])).
% 1.94/1.26  tff(c_79, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r2_hidden(C_34, B_33) | ~r2_hidden(C_34, A_32))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.26  tff(c_95, plain, (![C_35]: (~r2_hidden(C_35, '#skF_3'))), inference(resolution, [status(thm)], [c_56, c_79])).
% 1.94/1.26  tff(c_110, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_95])).
% 1.94/1.26  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.94/1.26  tff(c_29, plain, (![A_5]: (A_5='#skF_4' | ~v1_xboole_0(A_5))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6])).
% 1.94/1.26  tff(c_113, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_110, c_29])).
% 1.94/1.26  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_113])).
% 1.94/1.26  tff(c_118, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.94/1.26  tff(c_158, plain, (![A_50, B_51, C_52]: (~r1_xboole_0(A_50, B_51) | ~r2_hidden(C_52, B_51) | ~r2_hidden(C_52, A_50))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.94/1.26  tff(c_174, plain, (![C_53]: (~r2_hidden(C_53, '#skF_3'))), inference(resolution, [status(thm)], [c_118, c_158])).
% 1.94/1.26  tff(c_189, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_4, c_174])).
% 1.94/1.26  tff(c_192, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_189, c_6])).
% 1.94/1.26  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_192])).
% 1.94/1.26  tff(c_197, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 1.94/1.26  tff(c_199, plain, (![A_13]: (r1_xboole_0(A_13, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_197, c_16])).
% 1.94/1.26  tff(c_198, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.94/1.26  tff(c_204, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_198])).
% 1.94/1.26  tff(c_24, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.94/1.26  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_199, c_204, c_197, c_24])).
% 1.94/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.94/1.26  
% 1.94/1.26  Inference rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Ref     : 0
% 1.94/1.26  #Sup     : 40
% 1.94/1.26  #Fact    : 0
% 1.94/1.26  #Define  : 0
% 1.94/1.26  #Split   : 2
% 1.94/1.26  #Chain   : 0
% 1.94/1.26  #Close   : 0
% 1.94/1.26  
% 1.94/1.26  Ordering : KBO
% 1.94/1.26  
% 1.94/1.26  Simplification rules
% 1.94/1.26  ----------------------
% 1.94/1.26  #Subsume      : 10
% 1.94/1.26  #Demod        : 20
% 1.94/1.26  #Tautology    : 14
% 1.94/1.26  #SimpNegUnit  : 2
% 1.94/1.26  #BackRed      : 4
% 1.94/1.26  
% 1.94/1.26  #Partial instantiations: 0
% 1.94/1.26  #Strategies tried      : 1
% 1.94/1.26  
% 1.94/1.26  Timing (in seconds)
% 1.94/1.26  ----------------------
% 1.94/1.26  Preprocessing        : 0.28
% 1.94/1.26  Parsing              : 0.16
% 1.94/1.26  CNF conversion       : 0.02
% 1.94/1.26  Main loop            : 0.15
% 1.94/1.26  Inferencing          : 0.06
% 1.94/1.26  Reduction            : 0.04
% 1.94/1.26  Demodulation         : 0.03
% 1.94/1.26  BG Simplification    : 0.01
% 1.94/1.26  Subsumption          : 0.02
% 1.94/1.26  Abstraction          : 0.01
% 1.94/1.26  MUC search           : 0.00
% 1.94/1.26  Cooper               : 0.00
% 1.94/1.26  Total                : 0.46
% 1.94/1.26  Index Insertion      : 0.00
% 1.94/1.26  Index Deletion       : 0.00
% 1.94/1.26  Index Matching       : 0.00
% 1.94/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
