%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:25 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   50 (  95 expanded)
%              Number of leaves         :   16 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   62 ( 177 expanded)
%              Number of equality atoms :   27 (  93 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_74,negated_conjecture,(
    ~ ! [A] :
        ( ~ ( ~ r1_xboole_0(A,A)
            & A = k1_xboole_0 )
        & ~ ( A != k1_xboole_0
            & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_51,axiom,(
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

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_25,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | k1_xboole_0 = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_33,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_35,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_25])).

tff(c_66,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | A_10 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_14])).

tff(c_16,plain,(
    ! [A_12] : k3_xboole_0(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_34,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_33,c_16])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_xboole_0(A_1,B_2)
      | k3_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k3_xboole_0(A_18,B_19) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_4])).

tff(c_22,plain,
    ( r1_xboole_0('#skF_3','#skF_3')
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_48,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_58,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_53,c_48])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_58])).

tff(c_64,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_138,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,B_37)
      | ~ r2_hidden(C_38,A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [C_40] : ~ r2_hidden(C_40,'#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_138])).

tff(c_180,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_66,c_168])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_35,c_180])).

tff(c_187,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_250,plain,(
    ! [A_57,B_58,C_59] :
      ( ~ r1_xboole_0(A_57,B_58)
      | ~ r2_hidden(C_59,B_58)
      | ~ r2_hidden(C_59,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_260,plain,(
    ! [C_60] : ~ r2_hidden(C_60,'#skF_3') ),
    inference(resolution,[status(thm)],[c_187,c_250])).

tff(c_272,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_260])).

tff(c_278,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_272])).

tff(c_279,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_290,plain,(
    ! [A_12] : k3_xboole_0(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_279,c_16])).

tff(c_308,plain,(
    ! [A_65,B_66] :
      ( r1_xboole_0(A_65,B_66)
      | k3_xboole_0(A_65,B_66) != '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_4])).

tff(c_280,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_285,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_280])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_299,plain,(
    ~ r1_xboole_0('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_279,c_24])).

tff(c_313,plain,(
    k3_xboole_0('#skF_4','#skF_4') != '#skF_4' ),
    inference(resolution,[status(thm)],[c_308,c_299])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:56:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  %$ r2_hidden > r1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.96/1.23  
% 1.96/1.23  %Foreground sorts:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Background operators:
% 1.96/1.23  
% 1.96/1.23  
% 1.96/1.23  %Foreground operators:
% 1.96/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.96/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.96/1.23  
% 1.96/1.25  tff(f_74, negated_conjecture, ~(![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.96/1.25  tff(f_59, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.96/1.25  tff(f_61, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.96/1.25  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.96/1.25  tff(f_51, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.96/1.25  tff(c_20, plain, (k1_xboole_0!='#skF_3' | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.25  tff(c_25, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_20])).
% 1.96/1.25  tff(c_14, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.96/1.25  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_3') | k1_xboole_0='#skF_4'), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.25  tff(c_33, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_18])).
% 1.96/1.25  tff(c_35, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_33, c_25])).
% 1.96/1.25  tff(c_66, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | A_10='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_14])).
% 1.96/1.25  tff(c_16, plain, (![A_12]: (k3_xboole_0(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.96/1.25  tff(c_34, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_33, c_16])).
% 1.96/1.25  tff(c_4, plain, (![A_1, B_2]: (r1_xboole_0(A_1, B_2) | k3_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.96/1.25  tff(c_53, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k3_xboole_0(A_18, B_19)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_33, c_4])).
% 1.96/1.25  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_3') | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.25  tff(c_48, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_22])).
% 1.96/1.25  tff(c_58, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_53, c_48])).
% 1.96/1.25  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_58])).
% 1.96/1.25  tff(c_64, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 1.96/1.25  tff(c_138, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, B_37) | ~r2_hidden(C_38, A_36))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.25  tff(c_168, plain, (![C_40]: (~r2_hidden(C_40, '#skF_3'))), inference(resolution, [status(thm)], [c_64, c_138])).
% 1.96/1.25  tff(c_180, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_66, c_168])).
% 1.96/1.25  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_35, c_180])).
% 1.96/1.25  tff(c_187, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 1.96/1.25  tff(c_250, plain, (![A_57, B_58, C_59]: (~r1_xboole_0(A_57, B_58) | ~r2_hidden(C_59, B_58) | ~r2_hidden(C_59, A_57))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.96/1.25  tff(c_260, plain, (![C_60]: (~r2_hidden(C_60, '#skF_3'))), inference(resolution, [status(thm)], [c_187, c_250])).
% 1.96/1.25  tff(c_272, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_260])).
% 1.96/1.25  tff(c_278, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_272])).
% 1.96/1.25  tff(c_279, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_20])).
% 1.96/1.25  tff(c_290, plain, (![A_12]: (k3_xboole_0(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_279, c_16])).
% 1.96/1.25  tff(c_308, plain, (![A_65, B_66]: (r1_xboole_0(A_65, B_66) | k3_xboole_0(A_65, B_66)!='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_279, c_4])).
% 1.96/1.25  tff(c_280, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 1.96/1.25  tff(c_285, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_280])).
% 1.96/1.25  tff(c_24, plain, (k1_xboole_0!='#skF_3' | ~r1_xboole_0('#skF_4', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.25  tff(c_299, plain, (~r1_xboole_0('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_285, c_279, c_24])).
% 1.96/1.25  tff(c_313, plain, (k3_xboole_0('#skF_4', '#skF_4')!='#skF_4'), inference(resolution, [status(thm)], [c_308, c_299])).
% 1.96/1.25  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_313])).
% 1.96/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.25  
% 1.96/1.25  Inference rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Ref     : 0
% 1.96/1.25  #Sup     : 64
% 1.96/1.25  #Fact    : 0
% 1.96/1.25  #Define  : 0
% 1.96/1.25  #Split   : 3
% 1.96/1.25  #Chain   : 0
% 1.96/1.25  #Close   : 0
% 1.96/1.25  
% 1.96/1.25  Ordering : KBO
% 1.96/1.25  
% 1.96/1.25  Simplification rules
% 1.96/1.25  ----------------------
% 1.96/1.25  #Subsume      : 5
% 1.96/1.25  #Demod        : 32
% 1.96/1.25  #Tautology    : 37
% 1.96/1.25  #SimpNegUnit  : 4
% 1.96/1.25  #BackRed      : 2
% 1.96/1.25  
% 1.96/1.25  #Partial instantiations: 0
% 1.96/1.25  #Strategies tried      : 1
% 1.96/1.25  
% 1.96/1.25  Timing (in seconds)
% 1.96/1.25  ----------------------
% 1.96/1.25  Preprocessing        : 0.28
% 1.96/1.25  Parsing              : 0.15
% 1.96/1.25  CNF conversion       : 0.02
% 1.96/1.25  Main loop            : 0.19
% 1.96/1.25  Inferencing          : 0.08
% 1.96/1.25  Reduction            : 0.05
% 1.96/1.25  Demodulation         : 0.03
% 1.96/1.25  BG Simplification    : 0.01
% 1.96/1.25  Subsumption          : 0.03
% 1.96/1.25  Abstraction          : 0.01
% 1.96/1.25  MUC search           : 0.00
% 1.96/1.25  Cooper               : 0.00
% 1.96/1.25  Total                : 0.50
% 1.96/1.25  Index Insertion      : 0.00
% 1.96/1.25  Index Deletion       : 0.00
% 1.96/1.25  Index Matching       : 0.00
% 1.96/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
