%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:29 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  92 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_22,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_44,plain,(
    ! [B_24,A_25] :
      ( r1_xboole_0(B_24,A_25)
      | ~ r1_xboole_0(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_47,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_44])).

tff(c_183,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_xboole_0(A_36,C_37)
      | ~ r1_xboole_0(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_197,plain,(
    ! [A_40] :
      ( r1_xboole_0(A_40,'#skF_4')
      | ~ r1_tarski(A_40,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_47,c_183])).

tff(c_12,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_52,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_60,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k2_xboole_0(A_13,B_14)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_71,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_14])).

tff(c_83,plain,(
    ! [A_28,B_29] : k4_xboole_0(A_28,k4_xboole_0(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k3_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_71,c_83])).

tff(c_110,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_98])).

tff(c_6,plain,(
    ! [A_3,B_4,C_7] :
      ( ~ r1_xboole_0(A_3,B_4)
      | ~ r2_hidden(C_7,k3_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_122,plain,(
    ! [C_7] :
      ( ~ r1_xboole_0('#skF_3','#skF_4')
      | ~ r2_hidden(C_7,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_6])).

tff(c_153,plain,(
    ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_122])).

tff(c_202,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_197,c_153])).

tff(c_209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_202])).

tff(c_213,plain,(
    ! [C_41] : ~ r2_hidden(C_41,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_122])).

tff(c_217,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_213])).

tff(c_221,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_217])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:29:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.17  
% 1.87/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 1.87/1.17  
% 1.87/1.17  %Foreground sorts:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Background operators:
% 1.87/1.17  
% 1.87/1.17  
% 1.87/1.17  %Foreground operators:
% 1.87/1.17  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.87/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.87/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.87/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.87/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.87/1.17  
% 1.87/1.18  tff(f_76, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 1.87/1.18  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.87/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.87/1.18  tff(f_67, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.87/1.18  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.87/1.18  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.87/1.18  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 1.87/1.18  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.87/1.18  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.87/1.18  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.87/1.18  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.87/1.18  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.87/1.18  tff(c_22, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.87/1.18  tff(c_44, plain, (![B_24, A_25]: (r1_xboole_0(B_24, A_25) | ~r1_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.87/1.18  tff(c_47, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_44])).
% 1.87/1.18  tff(c_183, plain, (![A_36, C_37, B_38]: (r1_xboole_0(A_36, C_37) | ~r1_xboole_0(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_67])).
% 1.87/1.18  tff(c_197, plain, (![A_40]: (r1_xboole_0(A_40, '#skF_4') | ~r1_tarski(A_40, '#skF_5'))), inference(resolution, [status(thm)], [c_47, c_183])).
% 1.87/1.18  tff(c_12, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.87/1.18  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_76])).
% 1.87/1.18  tff(c_52, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.18  tff(c_60, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_26, c_52])).
% 1.87/1.18  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k2_xboole_0(A_13, B_14))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.18  tff(c_71, plain, (k4_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_60, c_14])).
% 1.87/1.18  tff(c_83, plain, (![A_28, B_29]: (k4_xboole_0(A_28, k4_xboole_0(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.87/1.18  tff(c_98, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k3_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_71, c_83])).
% 1.87/1.18  tff(c_110, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_98])).
% 1.87/1.18  tff(c_6, plain, (![A_3, B_4, C_7]: (~r1_xboole_0(A_3, B_4) | ~r2_hidden(C_7, k3_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.87/1.18  tff(c_122, plain, (![C_7]: (~r1_xboole_0('#skF_3', '#skF_4') | ~r2_hidden(C_7, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_110, c_6])).
% 1.87/1.18  tff(c_153, plain, (~r1_xboole_0('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_122])).
% 1.87/1.18  tff(c_202, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_197, c_153])).
% 1.87/1.18  tff(c_209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_202])).
% 1.87/1.18  tff(c_213, plain, (![C_41]: (~r2_hidden(C_41, '#skF_3'))), inference(splitRight, [status(thm)], [c_122])).
% 1.87/1.18  tff(c_217, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_213])).
% 1.87/1.18  tff(c_221, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_217])).
% 1.87/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.18  
% 1.87/1.18  Inference rules
% 1.87/1.18  ----------------------
% 1.87/1.18  #Ref     : 0
% 1.87/1.18  #Sup     : 54
% 1.87/1.18  #Fact    : 0
% 1.87/1.18  #Define  : 0
% 1.87/1.18  #Split   : 3
% 1.87/1.18  #Chain   : 0
% 1.87/1.18  #Close   : 0
% 1.87/1.18  
% 1.87/1.18  Ordering : KBO
% 1.87/1.18  
% 1.87/1.18  Simplification rules
% 1.87/1.19  ----------------------
% 1.87/1.19  #Subsume      : 0
% 1.87/1.19  #Demod        : 8
% 1.87/1.19  #Tautology    : 28
% 1.87/1.19  #SimpNegUnit  : 1
% 1.87/1.19  #BackRed      : 0
% 1.87/1.19  
% 1.87/1.19  #Partial instantiations: 0
% 1.87/1.19  #Strategies tried      : 1
% 1.87/1.19  
% 1.87/1.19  Timing (in seconds)
% 1.87/1.19  ----------------------
% 1.87/1.19  Preprocessing        : 0.27
% 1.87/1.19  Parsing              : 0.14
% 1.87/1.19  CNF conversion       : 0.02
% 1.87/1.19  Main loop            : 0.16
% 1.87/1.19  Inferencing          : 0.07
% 1.87/1.19  Reduction            : 0.05
% 1.87/1.19  Demodulation         : 0.03
% 1.87/1.19  BG Simplification    : 0.01
% 1.87/1.19  Subsumption          : 0.02
% 1.87/1.19  Abstraction          : 0.01
% 1.87/1.19  MUC search           : 0.00
% 1.87/1.19  Cooper               : 0.00
% 1.87/1.19  Total                : 0.46
% 1.87/1.19  Index Insertion      : 0.00
% 1.87/1.19  Index Deletion       : 0.00
% 1.87/1.19  Index Matching       : 0.00
% 1.87/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
