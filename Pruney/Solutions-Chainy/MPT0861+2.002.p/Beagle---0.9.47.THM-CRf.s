%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:01 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :   42 (  55 expanded)
%              Number of leaves         :   24 (  31 expanded)
%              Depth                    :    5
%              Number of atoms          :   48 (  84 expanded)
%              Number of equality atoms :   22 (  44 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_74,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_54,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_136,plain,(
    ! [A_61,C_62,B_63] :
      ( r2_hidden(k2_mcart_1(A_61),C_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(B_63,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_139,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_52,c_136])).

tff(c_140,plain,(
    ! [A_64,B_65,C_66] :
      ( r2_hidden(A_64,k4_xboole_0(B_65,k1_tarski(C_66)))
      | C_66 = A_64
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_155,plain,(
    ! [A_67,C_68,B_69] :
      ( ~ r2_hidden(A_67,k1_tarski(C_68))
      | C_68 = A_67
      | ~ r2_hidden(A_67,B_69) ) ),
    inference(resolution,[status(thm)],[c_140,c_4])).

tff(c_157,plain,(
    ! [B_69] :
      ( k2_mcart_1('#skF_3') = '#skF_6'
      | ~ r2_hidden(k2_mcart_1('#skF_3'),B_69) ) ),
    inference(resolution,[status(thm)],[c_139,c_155])).

tff(c_162,plain,(
    ! [B_69] : ~ r2_hidden(k2_mcart_1('#skF_3'),B_69) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_157])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_162,c_139])).

tff(c_168,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_56,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_174,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_168,c_56])).

tff(c_167,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_331,plain,(
    ! [A_122,C_123,B_124,D_125] :
      ( k1_mcart_1(A_122) = C_123
      | k1_mcart_1(A_122) = B_124
      | ~ r2_hidden(A_122,k2_zfmisc_1(k2_tarski(B_124,C_123),D_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_334,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_52,c_331])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_174,c_167,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 12:03:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  
% 2.08/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.30  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 2.08/1.30  
% 2.08/1.30  %Foreground sorts:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Background operators:
% 2.08/1.30  
% 2.08/1.30  
% 2.08/1.30  %Foreground operators:
% 2.08/1.30  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.08/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.08/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.08/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.08/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.08/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.08/1.30  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.30  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.08/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.08/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.08/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.30  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.08/1.30  
% 2.32/1.31  tff(f_83, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.32/1.31  tff(f_66, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.32/1.31  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.32/1.31  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.32/1.31  tff(f_74, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.32/1.31  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.32/1.31  tff(c_68, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_54])).
% 2.32/1.31  tff(c_52, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.32/1.31  tff(c_136, plain, (![A_61, C_62, B_63]: (r2_hidden(k2_mcart_1(A_61), C_62) | ~r2_hidden(A_61, k2_zfmisc_1(B_63, C_62)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.32/1.31  tff(c_139, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_136])).
% 2.32/1.31  tff(c_140, plain, (![A_64, B_65, C_66]: (r2_hidden(A_64, k4_xboole_0(B_65, k1_tarski(C_66))) | C_66=A_64 | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.32/1.31  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.32/1.31  tff(c_155, plain, (![A_67, C_68, B_69]: (~r2_hidden(A_67, k1_tarski(C_68)) | C_68=A_67 | ~r2_hidden(A_67, B_69))), inference(resolution, [status(thm)], [c_140, c_4])).
% 2.32/1.31  tff(c_157, plain, (![B_69]: (k2_mcart_1('#skF_3')='#skF_6' | ~r2_hidden(k2_mcart_1('#skF_3'), B_69))), inference(resolution, [status(thm)], [c_139, c_155])).
% 2.32/1.31  tff(c_162, plain, (![B_69]: (~r2_hidden(k2_mcart_1('#skF_3'), B_69))), inference(negUnitSimplification, [status(thm)], [c_68, c_157])).
% 2.32/1.31  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_162, c_139])).
% 2.32/1.31  tff(c_168, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_54])).
% 2.32/1.31  tff(c_56, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.32/1.31  tff(c_174, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_168, c_56])).
% 2.32/1.31  tff(c_167, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_54])).
% 2.32/1.31  tff(c_331, plain, (![A_122, C_123, B_124, D_125]: (k1_mcart_1(A_122)=C_123 | k1_mcart_1(A_122)=B_124 | ~r2_hidden(A_122, k2_zfmisc_1(k2_tarski(B_124, C_123), D_125)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.32/1.31  tff(c_334, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_52, c_331])).
% 2.32/1.31  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_174, c_167, c_334])).
% 2.32/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.32/1.31  
% 2.32/1.31  Inference rules
% 2.32/1.31  ----------------------
% 2.32/1.31  #Ref     : 0
% 2.32/1.31  #Sup     : 56
% 2.32/1.31  #Fact    : 0
% 2.32/1.31  #Define  : 0
% 2.32/1.31  #Split   : 1
% 2.32/1.31  #Chain   : 0
% 2.32/1.31  #Close   : 0
% 2.32/1.31  
% 2.32/1.31  Ordering : KBO
% 2.32/1.31  
% 2.32/1.31  Simplification rules
% 2.32/1.31  ----------------------
% 2.32/1.31  #Subsume      : 5
% 2.32/1.31  #Demod        : 13
% 2.32/1.31  #Tautology    : 34
% 2.32/1.31  #SimpNegUnit  : 3
% 2.32/1.31  #BackRed      : 1
% 2.32/1.31  
% 2.32/1.31  #Partial instantiations: 0
% 2.32/1.31  #Strategies tried      : 1
% 2.32/1.31  
% 2.32/1.31  Timing (in seconds)
% 2.32/1.31  ----------------------
% 2.32/1.32  Preprocessing        : 0.32
% 2.32/1.32  Parsing              : 0.17
% 2.32/1.32  CNF conversion       : 0.02
% 2.32/1.32  Main loop            : 0.22
% 2.32/1.32  Inferencing          : 0.08
% 2.32/1.32  Reduction            : 0.06
% 2.32/1.32  Demodulation         : 0.05
% 2.32/1.32  BG Simplification    : 0.01
% 2.32/1.32  Subsumption          : 0.04
% 2.32/1.32  Abstraction          : 0.01
% 2.32/1.32  MUC search           : 0.00
% 2.32/1.32  Cooper               : 0.00
% 2.32/1.32  Total                : 0.57
% 2.32/1.32  Index Insertion      : 0.00
% 2.32/1.32  Index Deletion       : 0.00
% 2.32/1.32  Index Matching       : 0.00
% 2.32/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
