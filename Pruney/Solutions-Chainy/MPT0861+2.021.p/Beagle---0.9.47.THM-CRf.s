%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:03 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    5
%              Number of atoms          :   49 (  81 expanded)
%              Number of equality atoms :   31 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(c_36,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_46,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_57,plain,(
    ! [A_47,C_48,B_49] :
      ( r2_hidden(k2_mcart_1(A_47),C_48)
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_49,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_32,c_57])).

tff(c_4,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_121,plain,(
    ! [A_78,B_79,C_80] :
      ( k4_xboole_0(k1_enumset1(A_78,B_79,C_80),k1_tarski(A_78)) = k2_tarski(B_79,C_80)
      | C_80 = A_78
      | B_79 = A_78 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [C_34,B_33] : ~ r2_hidden(C_34,k4_xboole_0(B_33,k1_tarski(C_34))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_143,plain,(
    ! [A_81,B_82,C_83] :
      ( ~ r2_hidden(A_81,k2_tarski(B_82,C_83))
      | C_83 = A_81
      | B_82 = A_81 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_20])).

tff(c_152,plain,(
    ! [A_84,A_85] :
      ( ~ r2_hidden(A_84,k1_tarski(A_85))
      | A_85 = A_84
      | A_85 = A_84 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_143])).

tff(c_155,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_152])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_155])).

tff(c_160,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_161,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_168,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_34])).

tff(c_217,plain,(
    ! [A_109,C_110,B_111,D_112] :
      ( k1_mcart_1(A_109) = C_110
      | k1_mcart_1(A_109) = B_111
      | ~ r2_hidden(A_109,k2_zfmisc_1(k2_tarski(B_111,C_110),D_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_220,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_32,c_217])).

tff(c_227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_160,c_168,c_220])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:12:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.97/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.97/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.97/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.97/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.97/1.21  
% 1.97/1.22  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.97/1.22  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.97/1.22  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.22  tff(f_35, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 1.97/1.22  tff(f_56, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.97/1.22  tff(f_70, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.97/1.22  tff(c_36, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.22  tff(c_46, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_32, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.22  tff(c_57, plain, (![A_47, C_48, B_49]: (r2_hidden(k2_mcart_1(A_47), C_48) | ~r2_hidden(A_47, k2_zfmisc_1(B_49, C_48)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.97/1.22  tff(c_60, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_57])).
% 1.97/1.22  tff(c_4, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_121, plain, (![A_78, B_79, C_80]: (k4_xboole_0(k1_enumset1(A_78, B_79, C_80), k1_tarski(A_78))=k2_tarski(B_79, C_80) | C_80=A_78 | B_79=A_78)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.22  tff(c_20, plain, (![C_34, B_33]: (~r2_hidden(C_34, k4_xboole_0(B_33, k1_tarski(C_34))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.97/1.22  tff(c_143, plain, (![A_81, B_82, C_83]: (~r2_hidden(A_81, k2_tarski(B_82, C_83)) | C_83=A_81 | B_82=A_81)), inference(superposition, [status(thm), theory('equality')], [c_121, c_20])).
% 1.97/1.22  tff(c_152, plain, (![A_84, A_85]: (~r2_hidden(A_84, k1_tarski(A_85)) | A_85=A_84 | A_85=A_84)), inference(superposition, [status(thm), theory('equality')], [c_4, c_143])).
% 1.97/1.22  tff(c_155, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_60, c_152])).
% 1.97/1.22  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_155])).
% 1.97/1.22  tff(c_160, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_161, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 1.97/1.22  tff(c_34, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.97/1.22  tff(c_168, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_34])).
% 1.97/1.22  tff(c_217, plain, (![A_109, C_110, B_111, D_112]: (k1_mcart_1(A_109)=C_110 | k1_mcart_1(A_109)=B_111 | ~r2_hidden(A_109, k2_zfmisc_1(k2_tarski(B_111, C_110), D_112)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.97/1.22  tff(c_220, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_32, c_217])).
% 1.97/1.22  tff(c_227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_160, c_168, c_220])).
% 1.97/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.22  
% 1.97/1.22  Inference rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Ref     : 0
% 1.97/1.22  #Sup     : 41
% 1.97/1.22  #Fact    : 0
% 1.97/1.22  #Define  : 0
% 1.97/1.22  #Split   : 2
% 1.97/1.22  #Chain   : 0
% 1.97/1.22  #Close   : 0
% 1.97/1.22  
% 1.97/1.22  Ordering : KBO
% 1.97/1.22  
% 1.97/1.22  Simplification rules
% 1.97/1.22  ----------------------
% 1.97/1.22  #Subsume      : 2
% 1.97/1.22  #Demod        : 3
% 1.97/1.22  #Tautology    : 28
% 1.97/1.22  #SimpNegUnit  : 2
% 1.97/1.22  #BackRed      : 1
% 1.97/1.22  
% 1.97/1.22  #Partial instantiations: 0
% 1.97/1.22  #Strategies tried      : 1
% 1.97/1.22  
% 1.97/1.22  Timing (in seconds)
% 1.97/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.31
% 1.97/1.22  Parsing              : 0.16
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.17
% 1.97/1.22  Inferencing          : 0.07
% 1.97/1.22  Reduction            : 0.05
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.02
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.50
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
