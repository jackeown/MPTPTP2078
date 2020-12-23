%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   40 (  69 expanded)
%              Number of leaves         :   14 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 126 expanded)
%              Number of equality atoms :   17 (  59 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_43,axiom,(
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

tff(c_14,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_21,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_22,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_20])).

tff(c_33,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | A_6 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_8])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_23,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_10])).

tff(c_16,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_32,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_23,c_16])).

tff(c_37,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ r1_xboole_0(A_16,B_17)
      | ~ r2_hidden(C_18,B_17)
      | ~ r2_hidden(C_18,A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_44,plain,(
    ! [C_19] : ~ r2_hidden(C_19,'#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_37])).

tff(c_56,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_33,c_44])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_56])).

tff(c_63,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_69,plain,(
    ! [A_25,B_26,C_27] :
      ( ~ r1_xboole_0(A_25,B_26)
      | ~ r2_hidden(C_27,B_26)
      | ~ r2_hidden(C_27,A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_76,plain,(
    ! [C_28] : ~ r2_hidden(C_28,'#skF_3') ),
    inference(resolution,[status(thm)],[c_63,c_69])).

tff(c_88,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_88])).

tff(c_95,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_97,plain,(
    ! [A_8] : r1_xboole_0(A_8,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_10])).

tff(c_96,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_102,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_96])).

tff(c_18,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_109,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_102,c_95,c_18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:43:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.17  %$ r2_hidden > r1_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.82/1.17  
% 1.82/1.17  %Foreground sorts:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Background operators:
% 1.82/1.17  
% 1.82/1.17  
% 1.82/1.17  %Foreground operators:
% 1.82/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.82/1.17  
% 1.82/1.18  tff(f_66, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.82/1.18  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.82/1.18  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.82/1.18  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.82/1.18  tff(c_14, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.82/1.18  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_14])).
% 1.82/1.18  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.18  tff(c_12, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.82/1.18  tff(c_21, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_12])).
% 1.82/1.18  tff(c_22, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_21, c_20])).
% 1.82/1.18  tff(c_33, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | A_6='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_21, c_8])).
% 1.82/1.18  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.18  tff(c_23, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_21, c_10])).
% 1.82/1.18  tff(c_16, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.82/1.18  tff(c_32, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_23, c_16])).
% 1.82/1.18  tff(c_37, plain, (![A_16, B_17, C_18]: (~r1_xboole_0(A_16, B_17) | ~r2_hidden(C_18, B_17) | ~r2_hidden(C_18, A_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.18  tff(c_44, plain, (![C_19]: (~r2_hidden(C_19, '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_37])).
% 1.82/1.18  tff(c_56, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_33, c_44])).
% 1.82/1.18  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_56])).
% 1.82/1.18  tff(c_63, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_12])).
% 1.82/1.18  tff(c_69, plain, (![A_25, B_26, C_27]: (~r1_xboole_0(A_25, B_26) | ~r2_hidden(C_27, B_26) | ~r2_hidden(C_27, A_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.82/1.18  tff(c_76, plain, (![C_28]: (~r2_hidden(C_28, '#skF_3'))), inference(resolution, [status(thm)], [c_63, c_69])).
% 1.82/1.18  tff(c_88, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_76])).
% 1.82/1.18  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_88])).
% 1.82/1.18  tff(c_95, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_14])).
% 1.82/1.18  tff(c_97, plain, (![A_8]: (r1_xboole_0(A_8, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_10])).
% 1.82/1.18  tff(c_96, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_14])).
% 1.82/1.18  tff(c_102, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_96])).
% 1.82/1.18  tff(c_18, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.82/1.18  tff(c_109, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_97, c_102, c_95, c_18])).
% 1.82/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.82/1.18  
% 1.82/1.18  Inference rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Ref     : 0
% 1.82/1.18  #Sup     : 16
% 1.82/1.18  #Fact    : 0
% 1.82/1.18  #Define  : 0
% 1.82/1.18  #Split   : 2
% 1.82/1.18  #Chain   : 0
% 1.82/1.18  #Close   : 0
% 1.82/1.18  
% 1.82/1.18  Ordering : KBO
% 1.82/1.18  
% 1.82/1.18  Simplification rules
% 1.82/1.18  ----------------------
% 1.82/1.18  #Subsume      : 2
% 1.82/1.18  #Demod        : 12
% 1.82/1.18  #Tautology    : 7
% 1.82/1.18  #SimpNegUnit  : 2
% 1.82/1.18  #BackRed      : 3
% 1.82/1.18  
% 1.82/1.18  #Partial instantiations: 0
% 1.82/1.18  #Strategies tried      : 1
% 1.82/1.18  
% 1.82/1.18  Timing (in seconds)
% 1.82/1.18  ----------------------
% 1.82/1.18  Preprocessing        : 0.27
% 1.82/1.18  Parsing              : 0.13
% 1.82/1.18  CNF conversion       : 0.02
% 1.82/1.18  Main loop            : 0.11
% 1.82/1.18  Inferencing          : 0.05
% 1.82/1.18  Reduction            : 0.03
% 1.82/1.18  Demodulation         : 0.02
% 1.82/1.18  BG Simplification    : 0.01
% 1.82/1.18  Subsumption          : 0.01
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.41
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
