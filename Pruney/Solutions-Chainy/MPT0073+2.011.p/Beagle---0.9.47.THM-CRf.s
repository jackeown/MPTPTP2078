%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:26 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   46 (  85 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   69 ( 165 expanded)
%              Number of equality atoms :   23 (  76 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_2','#skF_2')
    | k1_xboole_0 = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_36,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_37,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26])).

tff(c_16,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_38,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_16])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_2','#skF_2')
    | ~ r1_xboole_0('#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_47,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22])).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_1'(A_8),A_8)
      | A_8 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_14])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_72,plain,(
    ! [C_21,B_22,A_23] :
      ( ~ r2_hidden(C_21,B_22)
      | ~ r2_hidden(C_21,A_23)
      | ~ r2_hidden(C_21,k2_xboole_0(A_23,B_22))
      | ~ r1_xboole_0(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_81,plain,(
    ! [C_24,A_25] :
      ( ~ r2_hidden(C_24,A_25)
      | ~ r2_hidden(C_24,A_25)
      | ~ r2_hidden(C_24,A_25)
      | ~ r1_xboole_0(A_25,A_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_85,plain,(
    ! [A_26] :
      ( ~ r2_hidden('#skF_1'(A_26),A_26)
      | ~ r1_xboole_0(A_26,A_26)
      | A_26 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_48,c_81])).

tff(c_90,plain,(
    ! [A_27] :
      ( ~ r1_xboole_0(A_27,A_27)
      | A_27 = '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_48,c_85])).

tff(c_97,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_47,c_90])).

tff(c_107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_97])).

tff(c_108,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_125,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ r2_hidden(C_32,B_33)
      | ~ r2_hidden(C_32,A_34)
      | ~ r2_hidden(C_32,k2_xboole_0(A_34,B_33))
      | ~ r1_xboole_0(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_134,plain,(
    ! [C_35,A_36] :
      ( ~ r2_hidden(C_35,A_36)
      | ~ r2_hidden(C_35,A_36)
      | ~ r2_hidden(C_35,A_36)
      | ~ r1_xboole_0(A_36,A_36) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_138,plain,(
    ! [A_37] :
      ( ~ r2_hidden('#skF_1'(A_37),A_37)
      | ~ r1_xboole_0(A_37,A_37)
      | k1_xboole_0 = A_37 ) ),
    inference(resolution,[status(thm)],[c_14,c_134])).

tff(c_143,plain,(
    ! [A_38] :
      ( ~ r1_xboole_0(A_38,A_38)
      | k1_xboole_0 = A_38 ) ),
    inference(resolution,[status(thm)],[c_14,c_138])).

tff(c_150,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_108,c_143])).

tff(c_160,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_150])).

tff(c_161,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_164,plain,(
    ! [A_10] : r1_xboole_0(A_10,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_16])).

tff(c_162,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_169,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_162])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ r1_xboole_0('#skF_3','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_169,c_161,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:56:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  
% 1.86/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.18  %$ r2_hidden > r1_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.86/1.18  
% 1.86/1.18  %Foreground sorts:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Background operators:
% 1.86/1.18  
% 1.86/1.18  
% 1.86/1.18  %Foreground operators:
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.18  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.86/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.86/1.18  
% 1.86/1.19  tff(f_71, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.86/1.19  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.86/1.19  tff(f_56, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.86/1.19  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.86/1.19  tff(f_48, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_xboole_0)).
% 1.86/1.19  tff(c_20, plain, (k1_xboole_0!='#skF_2' | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.86/1.19  tff(c_26, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 1.86/1.19  tff(c_18, plain, (r1_xboole_0('#skF_2', '#skF_2') | k1_xboole_0='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.86/1.19  tff(c_36, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_18])).
% 1.86/1.19  tff(c_37, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_26])).
% 1.86/1.19  tff(c_16, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.86/1.19  tff(c_38, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_16])).
% 1.86/1.19  tff(c_22, plain, (r1_xboole_0('#skF_2', '#skF_2') | ~r1_xboole_0('#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.86/1.19  tff(c_47, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_22])).
% 1.86/1.19  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.86/1.19  tff(c_48, plain, (![A_8]: (r2_hidden('#skF_1'(A_8), A_8) | A_8='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_14])).
% 1.86/1.19  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.19  tff(c_72, plain, (![C_21, B_22, A_23]: (~r2_hidden(C_21, B_22) | ~r2_hidden(C_21, A_23) | ~r2_hidden(C_21, k2_xboole_0(A_23, B_22)) | ~r1_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.19  tff(c_81, plain, (![C_24, A_25]: (~r2_hidden(C_24, A_25) | ~r2_hidden(C_24, A_25) | ~r2_hidden(C_24, A_25) | ~r1_xboole_0(A_25, A_25))), inference(superposition, [status(thm), theory('equality')], [c_2, c_72])).
% 1.86/1.19  tff(c_85, plain, (![A_26]: (~r2_hidden('#skF_1'(A_26), A_26) | ~r1_xboole_0(A_26, A_26) | A_26='#skF_3')), inference(resolution, [status(thm)], [c_48, c_81])).
% 1.86/1.19  tff(c_90, plain, (![A_27]: (~r1_xboole_0(A_27, A_27) | A_27='#skF_3')), inference(resolution, [status(thm)], [c_48, c_85])).
% 1.86/1.19  tff(c_97, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_47, c_90])).
% 1.86/1.19  tff(c_107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_97])).
% 1.86/1.19  tff(c_108, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(splitRight, [status(thm)], [c_18])).
% 1.86/1.19  tff(c_125, plain, (![C_32, B_33, A_34]: (~r2_hidden(C_32, B_33) | ~r2_hidden(C_32, A_34) | ~r2_hidden(C_32, k2_xboole_0(A_34, B_33)) | ~r1_xboole_0(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.86/1.19  tff(c_134, plain, (![C_35, A_36]: (~r2_hidden(C_35, A_36) | ~r2_hidden(C_35, A_36) | ~r2_hidden(C_35, A_36) | ~r1_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_2, c_125])).
% 1.86/1.19  tff(c_138, plain, (![A_37]: (~r2_hidden('#skF_1'(A_37), A_37) | ~r1_xboole_0(A_37, A_37) | k1_xboole_0=A_37)), inference(resolution, [status(thm)], [c_14, c_134])).
% 1.86/1.19  tff(c_143, plain, (![A_38]: (~r1_xboole_0(A_38, A_38) | k1_xboole_0=A_38)), inference(resolution, [status(thm)], [c_14, c_138])).
% 1.86/1.19  tff(c_150, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_108, c_143])).
% 1.86/1.19  tff(c_160, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_150])).
% 1.86/1.19  tff(c_161, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.86/1.19  tff(c_164, plain, (![A_10]: (r1_xboole_0(A_10, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_161, c_16])).
% 1.86/1.19  tff(c_162, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 1.86/1.19  tff(c_169, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_162])).
% 1.86/1.19  tff(c_24, plain, (k1_xboole_0!='#skF_2' | ~r1_xboole_0('#skF_3', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 1.86/1.19  tff(c_186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_169, c_161, c_24])).
% 1.86/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.19  
% 1.86/1.19  Inference rules
% 1.86/1.19  ----------------------
% 1.86/1.19  #Ref     : 0
% 1.86/1.19  #Sup     : 32
% 1.86/1.19  #Fact    : 0
% 1.86/1.19  #Define  : 0
% 1.86/1.19  #Split   : 3
% 1.86/1.19  #Chain   : 0
% 1.86/1.19  #Close   : 0
% 1.86/1.19  
% 1.86/1.19  Ordering : KBO
% 1.86/1.20  
% 1.86/1.20  Simplification rules
% 1.86/1.20  ----------------------
% 1.86/1.20  #Subsume      : 4
% 1.86/1.20  #Demod        : 17
% 1.86/1.20  #Tautology    : 21
% 1.86/1.20  #SimpNegUnit  : 2
% 1.86/1.20  #BackRed      : 3
% 1.86/1.20  
% 1.86/1.20  #Partial instantiations: 0
% 1.86/1.20  #Strategies tried      : 1
% 1.86/1.20  
% 1.86/1.20  Timing (in seconds)
% 1.86/1.20  ----------------------
% 1.86/1.20  Preprocessing        : 0.28
% 1.86/1.20  Parsing              : 0.14
% 1.86/1.20  CNF conversion       : 0.02
% 1.86/1.20  Main loop            : 0.15
% 1.86/1.20  Inferencing          : 0.06
% 1.86/1.20  Reduction            : 0.04
% 1.86/1.20  Demodulation         : 0.03
% 1.86/1.20  BG Simplification    : 0.01
% 1.86/1.20  Subsumption          : 0.03
% 1.86/1.20  Abstraction          : 0.01
% 1.86/1.20  MUC search           : 0.00
% 1.86/1.20  Cooper               : 0.00
% 1.86/1.20  Total                : 0.46
% 1.86/1.20  Index Insertion      : 0.00
% 1.86/1.20  Index Deletion       : 0.00
% 1.86/1.20  Index Matching       : 0.00
% 1.86/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
