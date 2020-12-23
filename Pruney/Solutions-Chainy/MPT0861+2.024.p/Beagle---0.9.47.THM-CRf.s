%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   46 (  61 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  93 expanded)
%              Number of equality atoms :   32 (  64 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_45,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
    <=> ( r2_hidden(A,C)
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(c_32,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_62,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_92,plain,(
    ! [A_61,D_62,B_63,C_64] :
      ( r2_hidden(k2_mcart_1(A_61),D_62)
      | ~ r2_hidden(A_61,k2_zfmisc_1(k2_tarski(B_63,C_64),D_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_98,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_30,c_92])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_37,B_38] : k1_mcart_1(k4_tarski(A_37,B_38)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_29,D_32,C_31] :
      ( r2_hidden(k4_tarski(A_29,D_32),k2_zfmisc_1(C_31,k1_tarski(D_32)))
      | ~ r2_hidden(A_29,C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_127,plain,(
    ! [A_72,C_73,B_74,D_75] :
      ( k1_mcart_1(A_72) = C_73
      | k1_mcart_1(A_72) = B_74
      | ~ r2_hidden(A_72,k2_zfmisc_1(k2_tarski(B_74,C_73),D_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_131,plain,(
    ! [A_29,D_32,C_73,B_74] :
      ( k1_mcart_1(k4_tarski(A_29,D_32)) = C_73
      | k1_mcart_1(k4_tarski(A_29,D_32)) = B_74
      | ~ r2_hidden(A_29,k2_tarski(B_74,C_73)) ) ),
    inference(resolution,[status(thm)],[c_16,c_127])).

tff(c_147,plain,(
    ! [C_76,A_77,B_78] :
      ( C_76 = A_77
      | B_78 = A_77
      | ~ r2_hidden(A_77,k2_tarski(B_78,C_76)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_131])).

tff(c_151,plain,(
    ! [A_80,A_79] :
      ( A_80 = A_79
      | A_80 = A_79
      | ~ r2_hidden(A_79,k1_tarski(A_80)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_157,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_98,c_151])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_157])).

tff(c_165,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_171,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_34])).

tff(c_164,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_259,plain,(
    ! [A_122,C_123,B_124,D_125] :
      ( k1_mcart_1(A_122) = C_123
      | k1_mcart_1(A_122) = B_124
      | ~ r2_hidden(A_122,k2_zfmisc_1(k2_tarski(B_124,C_123),D_125)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_266,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_259])).

tff(c_275,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_171,c_164,c_266])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:35:29 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.28  
% 2.17/1.28  %Foreground sorts:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Background operators:
% 2.17/1.28  
% 2.17/1.28  
% 2.17/1.28  %Foreground operators:
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.17/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.28  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.17/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.28  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.17/1.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.28  
% 2.17/1.29  tff(f_66, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.17/1.29  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.17/1.29  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.29  tff(f_57, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.17/1.29  tff(f_45, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.17/1.29  tff(c_32, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.29  tff(c_62, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 2.17/1.29  tff(c_30, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.29  tff(c_92, plain, (![A_61, D_62, B_63, C_64]: (r2_hidden(k2_mcart_1(A_61), D_62) | ~r2_hidden(A_61, k2_zfmisc_1(k2_tarski(B_63, C_64), D_62)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.29  tff(c_98, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_92])).
% 2.17/1.29  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.29  tff(c_26, plain, (![A_37, B_38]: (k1_mcart_1(k4_tarski(A_37, B_38))=A_37)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.29  tff(c_16, plain, (![A_29, D_32, C_31]: (r2_hidden(k4_tarski(A_29, D_32), k2_zfmisc_1(C_31, k1_tarski(D_32))) | ~r2_hidden(A_29, C_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.29  tff(c_127, plain, (![A_72, C_73, B_74, D_75]: (k1_mcart_1(A_72)=C_73 | k1_mcart_1(A_72)=B_74 | ~r2_hidden(A_72, k2_zfmisc_1(k2_tarski(B_74, C_73), D_75)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.29  tff(c_131, plain, (![A_29, D_32, C_73, B_74]: (k1_mcart_1(k4_tarski(A_29, D_32))=C_73 | k1_mcart_1(k4_tarski(A_29, D_32))=B_74 | ~r2_hidden(A_29, k2_tarski(B_74, C_73)))), inference(resolution, [status(thm)], [c_16, c_127])).
% 2.17/1.29  tff(c_147, plain, (![C_76, A_77, B_78]: (C_76=A_77 | B_78=A_77 | ~r2_hidden(A_77, k2_tarski(B_78, C_76)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_131])).
% 2.17/1.29  tff(c_151, plain, (![A_80, A_79]: (A_80=A_79 | A_80=A_79 | ~r2_hidden(A_79, k1_tarski(A_80)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.17/1.29  tff(c_157, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_98, c_151])).
% 2.17/1.29  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_157])).
% 2.17/1.29  tff(c_165, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.17/1.29  tff(c_34, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.17/1.29  tff(c_171, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_165, c_34])).
% 2.17/1.29  tff(c_164, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.17/1.29  tff(c_259, plain, (![A_122, C_123, B_124, D_125]: (k1_mcart_1(A_122)=C_123 | k1_mcart_1(A_122)=B_124 | ~r2_hidden(A_122, k2_zfmisc_1(k2_tarski(B_124, C_123), D_125)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.29  tff(c_266, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_30, c_259])).
% 2.17/1.29  tff(c_275, plain, $false, inference(negUnitSimplification, [status(thm)], [c_171, c_164, c_266])).
% 2.17/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  Inference rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Ref     : 0
% 2.17/1.29  #Sup     : 48
% 2.17/1.29  #Fact    : 0
% 2.17/1.29  #Define  : 0
% 2.17/1.29  #Split   : 4
% 2.17/1.29  #Chain   : 0
% 2.17/1.29  #Close   : 0
% 2.17/1.29  
% 2.17/1.29  Ordering : KBO
% 2.17/1.29  
% 2.17/1.29  Simplification rules
% 2.17/1.29  ----------------------
% 2.17/1.29  #Subsume      : 1
% 2.17/1.29  #Demod        : 13
% 2.17/1.29  #Tautology    : 34
% 2.17/1.29  #SimpNegUnit  : 4
% 2.17/1.29  #BackRed      : 2
% 2.17/1.29  
% 2.17/1.29  #Partial instantiations: 0
% 2.17/1.29  #Strategies tried      : 1
% 2.17/1.29  
% 2.17/1.29  Timing (in seconds)
% 2.17/1.29  ----------------------
% 2.17/1.29  Preprocessing        : 0.30
% 2.17/1.29  Parsing              : 0.16
% 2.17/1.29  CNF conversion       : 0.02
% 2.17/1.29  Main loop            : 0.17
% 2.17/1.29  Inferencing          : 0.07
% 2.17/1.29  Reduction            : 0.05
% 2.17/1.29  Demodulation         : 0.04
% 2.17/1.29  BG Simplification    : 0.01
% 2.17/1.29  Subsumption          : 0.02
% 2.17/1.29  Abstraction          : 0.01
% 2.17/1.29  MUC search           : 0.00
% 2.17/1.29  Cooper               : 0.00
% 2.17/1.29  Total                : 0.50
% 2.17/1.29  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
