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
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 2.85s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   50 (  65 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   59 (  97 expanded)
%              Number of equality atoms :   13 (  23 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

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

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_20,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_98,plain,(
    ! [A_44,B_45,C_46] :
      ( ~ r1_xboole_0(A_44,B_45)
      | ~ r2_hidden(C_46,B_45)
      | ~ r2_hidden(C_46,A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_138,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,k1_tarski(A_56))
      | r2_hidden(A_56,B_55) ) ),
    inference(resolution,[status(thm)],[c_20,c_98])).

tff(c_697,plain,(
    ! [A_104,B_105,A_106] :
      ( ~ r2_hidden('#skF_1'(A_104,B_105),k1_tarski(A_106))
      | r2_hidden(A_106,A_104)
      | r1_xboole_0(A_104,B_105) ) ),
    inference(resolution,[status(thm)],[c_6,c_138])).

tff(c_828,plain,(
    ! [A_110,A_111] :
      ( r2_hidden(A_110,A_111)
      | r1_xboole_0(A_111,k1_tarski(A_110)) ) ),
    inference(resolution,[status(thm)],[c_4,c_697])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_857,plain,(
    ! [A_116,A_117] :
      ( k4_xboole_0(A_116,k1_tarski(A_117)) = A_116
      | r2_hidden(A_117,A_116) ) ),
    inference(resolution,[status(thm)],[c_828,c_10])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | r2_hidden('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_75,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_907,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_857,c_75])).

tff(c_934,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_907])).

tff(c_935,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_936,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_32,plain,
    ( k4_xboole_0('#skF_2',k1_tarski('#skF_3')) != '#skF_2'
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_994,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_32])).

tff(c_24,plain,(
    ! [C_20,B_19] : ~ r2_hidden(C_20,k4_xboole_0(B_19,k1_tarski(C_20))) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1001,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_994,c_24])).

tff(c_1006,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_935,c_1001])).

tff(c_1007,plain,(
    r2_hidden('#skF_5','#skF_4') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_1008,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1042,plain,(
    k4_xboole_0('#skF_4',k1_tarski('#skF_5')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_34])).

tff(c_1046,plain,(
    ~ r2_hidden('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1042,c_24])).

tff(c_1051,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1007,c_1046])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:25:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.85/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.52  
% 2.85/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.52  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.85/1.52  
% 2.85/1.52  %Foreground sorts:
% 2.85/1.52  
% 2.85/1.52  
% 2.85/1.52  %Background operators:
% 2.85/1.52  
% 2.85/1.52  
% 2.85/1.52  %Foreground operators:
% 2.85/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.52  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.52  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.52  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.52  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.52  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.52  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.85/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.85/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.52  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.52  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.85/1.52  
% 2.85/1.53  tff(f_73, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.85/1.53  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.85/1.53  tff(f_60, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.85/1.53  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.85/1.53  tff(f_67, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.85/1.53  tff(c_30, plain, (~r2_hidden('#skF_3', '#skF_2') | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.85/1.53  tff(c_44, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_30])).
% 2.85/1.53  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.53  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.53  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.85/1.53  tff(c_98, plain, (![A_44, B_45, C_46]: (~r1_xboole_0(A_44, B_45) | ~r2_hidden(C_46, B_45) | ~r2_hidden(C_46, A_44))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.85/1.53  tff(c_138, plain, (![C_54, B_55, A_56]: (~r2_hidden(C_54, B_55) | ~r2_hidden(C_54, k1_tarski(A_56)) | r2_hidden(A_56, B_55))), inference(resolution, [status(thm)], [c_20, c_98])).
% 2.85/1.53  tff(c_697, plain, (![A_104, B_105, A_106]: (~r2_hidden('#skF_1'(A_104, B_105), k1_tarski(A_106)) | r2_hidden(A_106, A_104) | r1_xboole_0(A_104, B_105))), inference(resolution, [status(thm)], [c_6, c_138])).
% 2.85/1.53  tff(c_828, plain, (![A_110, A_111]: (r2_hidden(A_110, A_111) | r1_xboole_0(A_111, k1_tarski(A_110)))), inference(resolution, [status(thm)], [c_4, c_697])).
% 2.85/1.53  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.85/1.53  tff(c_857, plain, (![A_116, A_117]: (k4_xboole_0(A_116, k1_tarski(A_117))=A_116 | r2_hidden(A_117, A_116))), inference(resolution, [status(thm)], [c_828, c_10])).
% 2.85/1.53  tff(c_28, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | r2_hidden('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.85/1.53  tff(c_75, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_28])).
% 2.85/1.53  tff(c_907, plain, (r2_hidden('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_857, c_75])).
% 2.85/1.53  tff(c_934, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_907])).
% 2.85/1.53  tff(c_935, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_28])).
% 2.85/1.53  tff(c_936, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.85/1.53  tff(c_32, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_3'))!='#skF_2' | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.85/1.53  tff(c_994, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_936, c_32])).
% 2.85/1.53  tff(c_24, plain, (![C_20, B_19]: (~r2_hidden(C_20, k4_xboole_0(B_19, k1_tarski(C_20))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.85/1.53  tff(c_1001, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_994, c_24])).
% 2.85/1.53  tff(c_1006, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_935, c_1001])).
% 2.85/1.53  tff(c_1007, plain, (r2_hidden('#skF_5', '#skF_4')), inference(splitRight, [status(thm)], [c_30])).
% 2.85/1.53  tff(c_1008, plain, (r2_hidden('#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_30])).
% 2.85/1.53  tff(c_34, plain, (~r2_hidden('#skF_3', '#skF_2') | k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.85/1.53  tff(c_1042, plain, (k4_xboole_0('#skF_4', k1_tarski('#skF_5'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_34])).
% 2.85/1.53  tff(c_1046, plain, (~r2_hidden('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1042, c_24])).
% 2.85/1.53  tff(c_1051, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1007, c_1046])).
% 2.85/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.53  
% 2.85/1.53  Inference rules
% 2.85/1.53  ----------------------
% 2.85/1.53  #Ref     : 0
% 2.85/1.53  #Sup     : 248
% 2.85/1.53  #Fact    : 0
% 2.85/1.53  #Define  : 0
% 2.85/1.53  #Split   : 2
% 2.85/1.53  #Chain   : 0
% 2.85/1.53  #Close   : 0
% 2.85/1.53  
% 2.85/1.53  Ordering : KBO
% 2.85/1.53  
% 2.85/1.53  Simplification rules
% 2.85/1.53  ----------------------
% 2.85/1.53  #Subsume      : 82
% 2.85/1.53  #Demod        : 5
% 2.85/1.53  #Tautology    : 52
% 2.85/1.53  #SimpNegUnit  : 1
% 2.85/1.53  #BackRed      : 0
% 2.85/1.53  
% 2.85/1.53  #Partial instantiations: 0
% 2.85/1.53  #Strategies tried      : 1
% 2.85/1.53  
% 2.85/1.53  Timing (in seconds)
% 2.85/1.53  ----------------------
% 2.85/1.53  Preprocessing        : 0.29
% 2.85/1.53  Parsing              : 0.15
% 2.85/1.53  CNF conversion       : 0.02
% 2.85/1.53  Main loop            : 0.36
% 2.85/1.53  Inferencing          : 0.15
% 2.85/1.53  Reduction            : 0.08
% 2.85/1.53  Demodulation         : 0.04
% 2.85/1.53  BG Simplification    : 0.02
% 2.85/1.53  Subsumption          : 0.08
% 2.85/1.53  Abstraction          : 0.02
% 2.85/1.53  MUC search           : 0.00
% 2.85/1.53  Cooper               : 0.00
% 2.85/1.53  Total                : 0.68
% 2.85/1.53  Index Insertion      : 0.00
% 2.85/1.53  Index Deletion       : 0.00
% 2.85/1.53  Index Matching       : 0.00
% 2.85/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
