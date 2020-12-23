%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   51 (  70 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   56 (  94 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_22,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_39,plain,(
    ! [A_22,B_23] :
      ( r1_xboole_0(k1_tarski(A_22),B_23)
      | r2_hidden(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_74,plain,(
    ! [B_30,A_31] :
      ( r1_xboole_0(B_30,k1_tarski(A_31))
      | r2_hidden(A_31,B_30) ) ),
    inference(resolution,[status(thm)],[c_39,c_2])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = A_5
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [B_39,A_40] :
      ( k4_xboole_0(B_39,k1_tarski(A_40)) = B_39
      | r2_hidden(A_40,B_39) ) ),
    inference(resolution,[status(thm)],[c_74,c_6])).

tff(c_20,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_109,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_125,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_109])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_125])).

tff(c_134,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_135,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_141,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_24])).

tff(c_61,plain,(
    ! [A_28,B_29] :
      ( r1_xboole_0(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(B_32,A_33)
      | k4_xboole_0(A_33,B_32) != A_33 ) ),
    inference(resolution,[status(thm)],[c_61,c_2])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( ~ r2_hidden(A_13,B_14)
      | ~ r1_xboole_0(k1_tarski(A_13),B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_211,plain,(
    ! [A_50,A_51] :
      ( ~ r2_hidden(A_50,A_51)
      | k4_xboole_0(A_51,k1_tarski(A_50)) != A_51 ) ),
    inference(resolution,[status(thm)],[c_87,c_16])).

tff(c_217,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_211])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_217])).

tff(c_226,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_227,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_293,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_26])).

tff(c_253,plain,(
    ! [A_62,B_63] :
      ( r1_xboole_0(A_62,B_63)
      | k4_xboole_0(A_62,B_63) != A_62 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_279,plain,(
    ! [B_66,A_67] :
      ( r1_xboole_0(B_66,A_67)
      | k4_xboole_0(A_67,B_66) != A_67 ) ),
    inference(resolution,[status(thm)],[c_253,c_2])).

tff(c_321,plain,(
    ! [A_74,A_75] :
      ( ~ r2_hidden(A_74,A_75)
      | k4_xboole_0(A_75,k1_tarski(A_74)) != A_75 ) ),
    inference(resolution,[status(thm)],[c_279,c_16])).

tff(c_324,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_321])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_324])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:54:47 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.24  
% 2.05/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.25  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.05/1.25  
% 2.05/1.25  %Foreground sorts:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Background operators:
% 2.05/1.25  
% 2.05/1.25  
% 2.05/1.25  %Foreground operators:
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.05/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.05/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.25  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.05/1.25  
% 2.05/1.26  tff(f_57, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.05/1.26  tff(f_51, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.05/1.26  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.05/1.26  tff(f_35, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.05/1.26  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.05/1.26  tff(c_22, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.26  tff(c_36, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_22])).
% 2.05/1.26  tff(c_39, plain, (![A_22, B_23]: (r1_xboole_0(k1_tarski(A_22), B_23) | r2_hidden(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.26  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.05/1.26  tff(c_74, plain, (![B_30, A_31]: (r1_xboole_0(B_30, k1_tarski(A_31)) | r2_hidden(A_31, B_30))), inference(resolution, [status(thm)], [c_39, c_2])).
% 2.05/1.26  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=A_5 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.26  tff(c_119, plain, (![B_39, A_40]: (k4_xboole_0(B_39, k1_tarski(A_40))=B_39 | r2_hidden(A_40, B_39))), inference(resolution, [status(thm)], [c_74, c_6])).
% 2.05/1.26  tff(c_20, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.26  tff(c_109, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_20])).
% 2.05/1.26  tff(c_125, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_119, c_109])).
% 2.05/1.26  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_125])).
% 2.05/1.26  tff(c_134, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.05/1.26  tff(c_135, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_20])).
% 2.05/1.26  tff(c_24, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.26  tff(c_141, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_24])).
% 2.05/1.26  tff(c_61, plain, (![A_28, B_29]: (r1_xboole_0(A_28, B_29) | k4_xboole_0(A_28, B_29)!=A_28)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.26  tff(c_87, plain, (![B_32, A_33]: (r1_xboole_0(B_32, A_33) | k4_xboole_0(A_33, B_32)!=A_33)), inference(resolution, [status(thm)], [c_61, c_2])).
% 2.05/1.26  tff(c_16, plain, (![A_13, B_14]: (~r2_hidden(A_13, B_14) | ~r1_xboole_0(k1_tarski(A_13), B_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.26  tff(c_211, plain, (![A_50, A_51]: (~r2_hidden(A_50, A_51) | k4_xboole_0(A_51, k1_tarski(A_50))!=A_51)), inference(resolution, [status(thm)], [c_87, c_16])).
% 2.05/1.26  tff(c_217, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_141, c_211])).
% 2.05/1.26  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_217])).
% 2.05/1.26  tff(c_226, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_22])).
% 2.05/1.26  tff(c_227, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_22])).
% 2.05/1.26  tff(c_26, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.05/1.26  tff(c_293, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_227, c_26])).
% 2.05/1.26  tff(c_253, plain, (![A_62, B_63]: (r1_xboole_0(A_62, B_63) | k4_xboole_0(A_62, B_63)!=A_62)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.05/1.26  tff(c_279, plain, (![B_66, A_67]: (r1_xboole_0(B_66, A_67) | k4_xboole_0(A_67, B_66)!=A_67)), inference(resolution, [status(thm)], [c_253, c_2])).
% 2.05/1.26  tff(c_321, plain, (![A_74, A_75]: (~r2_hidden(A_74, A_75) | k4_xboole_0(A_75, k1_tarski(A_74))!=A_75)), inference(resolution, [status(thm)], [c_279, c_16])).
% 2.05/1.26  tff(c_324, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_293, c_321])).
% 2.05/1.26  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_226, c_324])).
% 2.05/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.05/1.26  
% 2.05/1.26  Inference rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Ref     : 0
% 2.05/1.26  #Sup     : 70
% 2.05/1.26  #Fact    : 0
% 2.05/1.26  #Define  : 0
% 2.05/1.26  #Split   : 2
% 2.05/1.26  #Chain   : 0
% 2.05/1.26  #Close   : 0
% 2.05/1.26  
% 2.05/1.26  Ordering : KBO
% 2.05/1.26  
% 2.05/1.26  Simplification rules
% 2.05/1.26  ----------------------
% 2.05/1.26  #Subsume      : 5
% 2.05/1.26  #Demod        : 11
% 2.05/1.26  #Tautology    : 43
% 2.05/1.26  #SimpNegUnit  : 3
% 2.05/1.26  #BackRed      : 0
% 2.05/1.26  
% 2.05/1.26  #Partial instantiations: 0
% 2.05/1.26  #Strategies tried      : 1
% 2.05/1.26  
% 2.05/1.26  Timing (in seconds)
% 2.05/1.26  ----------------------
% 2.05/1.26  Preprocessing        : 0.29
% 2.05/1.26  Parsing              : 0.16
% 2.05/1.26  CNF conversion       : 0.02
% 2.05/1.26  Main loop            : 0.19
% 2.05/1.26  Inferencing          : 0.08
% 2.05/1.26  Reduction            : 0.05
% 2.05/1.26  Demodulation         : 0.03
% 2.05/1.26  BG Simplification    : 0.01
% 2.05/1.26  Subsumption          : 0.03
% 2.05/1.26  Abstraction          : 0.01
% 2.05/1.26  MUC search           : 0.00
% 2.05/1.26  Cooper               : 0.00
% 2.05/1.26  Total                : 0.52
% 2.05/1.26  Index Insertion      : 0.00
% 2.05/1.26  Index Deletion       : 0.00
% 2.05/1.26  Index Matching       : 0.00
% 2.05/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
