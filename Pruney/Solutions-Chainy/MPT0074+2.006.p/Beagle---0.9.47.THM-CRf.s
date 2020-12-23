%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:27 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   46 (  84 expanded)
%              Number of leaves         :   18 (  37 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 190 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_67,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(B,C) )
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_54,axiom,(
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

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_24,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_129,plain,(
    ! [C_38,B_39,A_40] :
      ( r2_hidden(C_38,B_39)
      | ~ r2_hidden(C_38,A_40)
      | ~ r1_tarski(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_136,plain,(
    ! [A_1,B_2,B_39] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_39)
      | ~ r1_tarski(A_1,B_39)
      | r1_tarski(A_1,B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_220,plain,(
    ! [A_52,B_53,B_54] :
      ( r2_hidden('#skF_1'(A_52,B_53),B_54)
      | ~ r1_tarski(A_52,B_54)
      | r1_tarski(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_6,c_129])).

tff(c_22,plain,(
    r1_xboole_0('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_72,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,B_31)
      | ~ r2_hidden(C_32,A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_78,plain,(
    ! [C_32] :
      ( ~ r2_hidden(C_32,'#skF_5')
      | ~ r2_hidden(C_32,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_265,plain,(
    ! [A_58,B_59] :
      ( ~ r2_hidden('#skF_1'(A_58,B_59),'#skF_4')
      | ~ r1_tarski(A_58,'#skF_5')
      | r1_tarski(A_58,B_59) ) ),
    inference(resolution,[status(thm)],[c_220,c_78])).

tff(c_276,plain,(
    ! [A_60,B_61] :
      ( ~ r1_tarski(A_60,'#skF_5')
      | ~ r1_tarski(A_60,'#skF_4')
      | r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_136,c_265])).

tff(c_281,plain,(
    ! [B_61] :
      ( ~ r1_tarski('#skF_3','#skF_4')
      | r1_tarski('#skF_3',B_61) ) ),
    inference(resolution,[status(thm)],[c_24,c_276])).

tff(c_288,plain,(
    ! [B_62] : r1_tarski('#skF_3',B_62) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_281])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k3_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_310,plain,(
    ! [B_62] : k3_xboole_0('#skF_3',B_62) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_288,c_18])).

tff(c_285,plain,(
    ! [B_61] : r1_tarski('#skF_3',B_61) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_281])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),A_8)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_362,plain,(
    ! [A_68,B_69,B_70] :
      ( r2_hidden('#skF_2'(A_68,B_69),B_70)
      | ~ r1_tarski(A_68,B_70)
      | r1_xboole_0(A_68,B_69) ) ),
    inference(resolution,[status(thm)],[c_16,c_129])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_88,plain,(
    ! [C_34] :
      ( ~ r2_hidden(C_34,'#skF_5')
      | ~ r2_hidden(C_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_22,c_72])).

tff(c_103,plain,(
    ! [A_8] :
      ( ~ r2_hidden('#skF_2'(A_8,'#skF_5'),'#skF_4')
      | r1_xboole_0(A_8,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_14,c_88])).

tff(c_395,plain,(
    ! [A_71] :
      ( ~ r1_tarski(A_71,'#skF_4')
      | r1_xboole_0(A_71,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_362,c_103])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = k1_xboole_0
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_403,plain,(
    ! [A_72] :
      ( k3_xboole_0(A_72,'#skF_5') = k1_xboole_0
      | ~ r1_tarski(A_72,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_395,c_8])).

tff(c_407,plain,(
    k3_xboole_0('#skF_3','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_285,c_403])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_407])).

tff(c_415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_413])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  %$ r2_hidden > r1_xboole_0 > r1_tarski > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.47/1.39  
% 2.47/1.39  %Foreground sorts:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Background operators:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Foreground operators:
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.39  tff('#skF_5', type, '#skF_5': $i).
% 2.47/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.47/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.39  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.47/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.47/1.39  
% 2.47/1.41  tff(f_67, negated_conjecture, ~(![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_xboole_1)).
% 2.47/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.47/1.41  tff(f_54, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.47/1.41  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.47/1.41  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.47/1.41  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.41  tff(c_26, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.41  tff(c_24, plain, (r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.41  tff(c_129, plain, (![C_38, B_39, A_40]: (r2_hidden(C_38, B_39) | ~r2_hidden(C_38, A_40) | ~r1_tarski(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.47/1.41  tff(c_136, plain, (![A_1, B_2, B_39]: (r2_hidden('#skF_1'(A_1, B_2), B_39) | ~r1_tarski(A_1, B_39) | r1_tarski(A_1, B_2))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.47/1.41  tff(c_220, plain, (![A_52, B_53, B_54]: (r2_hidden('#skF_1'(A_52, B_53), B_54) | ~r1_tarski(A_52, B_54) | r1_tarski(A_52, B_53))), inference(resolution, [status(thm)], [c_6, c_129])).
% 2.47/1.41  tff(c_22, plain, (r1_xboole_0('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.47/1.41  tff(c_72, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, B_31) | ~r2_hidden(C_32, A_30))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.41  tff(c_78, plain, (![C_32]: (~r2_hidden(C_32, '#skF_5') | ~r2_hidden(C_32, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.47/1.41  tff(c_265, plain, (![A_58, B_59]: (~r2_hidden('#skF_1'(A_58, B_59), '#skF_4') | ~r1_tarski(A_58, '#skF_5') | r1_tarski(A_58, B_59))), inference(resolution, [status(thm)], [c_220, c_78])).
% 2.47/1.41  tff(c_276, plain, (![A_60, B_61]: (~r1_tarski(A_60, '#skF_5') | ~r1_tarski(A_60, '#skF_4') | r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_136, c_265])).
% 2.47/1.41  tff(c_281, plain, (![B_61]: (~r1_tarski('#skF_3', '#skF_4') | r1_tarski('#skF_3', B_61))), inference(resolution, [status(thm)], [c_24, c_276])).
% 2.47/1.41  tff(c_288, plain, (![B_62]: (r1_tarski('#skF_3', B_62))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_281])).
% 2.47/1.41  tff(c_18, plain, (![A_13, B_14]: (k3_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.47/1.41  tff(c_310, plain, (![B_62]: (k3_xboole_0('#skF_3', B_62)='#skF_3')), inference(resolution, [status(thm)], [c_288, c_18])).
% 2.47/1.41  tff(c_285, plain, (![B_61]: (r1_tarski('#skF_3', B_61))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_281])).
% 2.47/1.41  tff(c_16, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), A_8) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.41  tff(c_362, plain, (![A_68, B_69, B_70]: (r2_hidden('#skF_2'(A_68, B_69), B_70) | ~r1_tarski(A_68, B_70) | r1_xboole_0(A_68, B_69))), inference(resolution, [status(thm)], [c_16, c_129])).
% 2.47/1.41  tff(c_14, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.47/1.41  tff(c_88, plain, (![C_34]: (~r2_hidden(C_34, '#skF_5') | ~r2_hidden(C_34, '#skF_4'))), inference(resolution, [status(thm)], [c_22, c_72])).
% 2.47/1.41  tff(c_103, plain, (![A_8]: (~r2_hidden('#skF_2'(A_8, '#skF_5'), '#skF_4') | r1_xboole_0(A_8, '#skF_5'))), inference(resolution, [status(thm)], [c_14, c_88])).
% 2.47/1.41  tff(c_395, plain, (![A_71]: (~r1_tarski(A_71, '#skF_4') | r1_xboole_0(A_71, '#skF_5'))), inference(resolution, [status(thm)], [c_362, c_103])).
% 2.47/1.41  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=k1_xboole_0 | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.47/1.41  tff(c_403, plain, (![A_72]: (k3_xboole_0(A_72, '#skF_5')=k1_xboole_0 | ~r1_tarski(A_72, '#skF_4'))), inference(resolution, [status(thm)], [c_395, c_8])).
% 2.47/1.41  tff(c_407, plain, (k3_xboole_0('#skF_3', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_285, c_403])).
% 2.47/1.41  tff(c_413, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_310, c_407])).
% 2.47/1.41  tff(c_415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_413])).
% 2.47/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.41  
% 2.47/1.41  Inference rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Ref     : 0
% 2.47/1.41  #Sup     : 92
% 2.47/1.41  #Fact    : 0
% 2.47/1.41  #Define  : 0
% 2.47/1.41  #Split   : 2
% 2.47/1.41  #Chain   : 0
% 2.47/1.41  #Close   : 0
% 2.47/1.41  
% 2.47/1.41  Ordering : KBO
% 2.47/1.41  
% 2.47/1.41  Simplification rules
% 2.47/1.41  ----------------------
% 2.47/1.41  #Subsume      : 7
% 2.47/1.41  #Demod        : 13
% 2.47/1.41  #Tautology    : 30
% 2.47/1.41  #SimpNegUnit  : 1
% 2.47/1.41  #BackRed      : 0
% 2.47/1.41  
% 2.47/1.41  #Partial instantiations: 0
% 2.47/1.41  #Strategies tried      : 1
% 2.47/1.41  
% 2.47/1.41  Timing (in seconds)
% 2.47/1.41  ----------------------
% 2.47/1.41  Preprocessing        : 0.30
% 2.47/1.41  Parsing              : 0.16
% 2.47/1.41  CNF conversion       : 0.02
% 2.47/1.41  Main loop            : 0.28
% 2.47/1.41  Inferencing          : 0.11
% 2.47/1.41  Reduction            : 0.07
% 2.47/1.41  Demodulation         : 0.05
% 2.47/1.41  BG Simplification    : 0.02
% 2.47/1.41  Subsumption          : 0.07
% 2.47/1.41  Abstraction          : 0.01
% 2.47/1.41  MUC search           : 0.00
% 2.47/1.41  Cooper               : 0.00
% 2.47/1.41  Total                : 0.62
% 2.47/1.41  Index Insertion      : 0.00
% 2.47/1.41  Index Deletion       : 0.00
% 2.47/1.41  Index Matching       : 0.00
% 2.47/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
