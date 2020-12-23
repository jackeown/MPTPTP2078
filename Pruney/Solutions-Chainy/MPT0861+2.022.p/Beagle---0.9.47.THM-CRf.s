%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:04 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   41 (  52 expanded)
%              Number of leaves         :   21 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   46 (  78 expanded)
%              Number of equality atoms :   28 (  48 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(c_26,plain,
    ( k1_mcart_1('#skF_1') != '#skF_3'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_38,plain,(
    k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_50,plain,(
    ! [A_24,C_25,B_26] :
      ( r2_hidden(k2_mcart_1(A_24),C_25)
      | ~ r2_hidden(A_24,k2_zfmisc_1(B_26,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_53,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_24,c_50])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(k1_tarski(A_33),k1_tarski(B_34)) = k1_tarski(A_33)
      | B_34 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    ! [C_14,B_13] : ~ r2_hidden(C_14,k4_xboole_0(B_13,k1_tarski(C_14))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [B_35,A_36] :
      ( ~ r2_hidden(B_35,k1_tarski(A_36))
      | B_35 = A_36 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_16])).

tff(c_89,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_53,c_86])).

tff(c_93,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_89])).

tff(c_95,plain,(
    k2_mcart_1('#skF_1') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_28,plain,
    ( k1_mcart_1('#skF_1') != '#skF_2'
    | k2_mcart_1('#skF_1') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_101,plain,(
    k1_mcart_1('#skF_1') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_28])).

tff(c_94,plain,(
    k1_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_113,plain,(
    ! [A_42,B_43,C_44] :
      ( r2_hidden(k1_mcart_1(A_42),B_43)
      | ~ r2_hidden(A_42,k2_zfmisc_1(B_43,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_116,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_113])).

tff(c_176,plain,(
    ! [A_61,B_62,C_63] :
      ( k4_xboole_0(k1_enumset1(A_61,B_62,C_63),k1_tarski(A_61)) = k2_tarski(B_62,C_63)
      | C_63 = A_61
      | B_62 = A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_198,plain,(
    ! [A_64,B_65,C_66] :
      ( ~ r2_hidden(A_64,k2_tarski(B_65,C_66))
      | C_66 = A_64
      | B_65 = A_64 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_16])).

tff(c_201,plain,
    ( k1_mcart_1('#skF_1') = '#skF_3'
    | k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_116,c_198])).

tff(c_208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_101,c_94,c_201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:30:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.40  
% 2.02/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.41  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.02/1.41  
% 2.02/1.41  %Foreground sorts:
% 2.02/1.41  
% 2.02/1.41  
% 2.02/1.41  %Background operators:
% 2.02/1.41  
% 2.02/1.41  
% 2.02/1.41  %Foreground operators:
% 2.02/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.02/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.02/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.02/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.02/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.02/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.02/1.41  tff('#skF_2', type, '#skF_2': $i).
% 2.02/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.02/1.41  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.02/1.41  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.02/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.02/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.02/1.41  
% 2.02/1.42  tff(f_68, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 2.02/1.42  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.02/1.42  tff(f_46, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.02/1.42  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.02/1.42  tff(f_35, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 2.02/1.42  tff(c_26, plain, (k1_mcart_1('#skF_1')!='#skF_3' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.42  tff(c_38, plain, (k2_mcart_1('#skF_1')!='#skF_4'), inference(splitLeft, [status(thm)], [c_26])).
% 2.02/1.42  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.42  tff(c_50, plain, (![A_24, C_25, B_26]: (r2_hidden(k2_mcart_1(A_24), C_25) | ~r2_hidden(A_24, k2_zfmisc_1(B_26, C_25)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.42  tff(c_53, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_50])).
% 2.02/1.42  tff(c_65, plain, (![A_33, B_34]: (k4_xboole_0(k1_tarski(A_33), k1_tarski(B_34))=k1_tarski(A_33) | B_34=A_33)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.42  tff(c_16, plain, (![C_14, B_13]: (~r2_hidden(C_14, k4_xboole_0(B_13, k1_tarski(C_14))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.42  tff(c_86, plain, (![B_35, A_36]: (~r2_hidden(B_35, k1_tarski(A_36)) | B_35=A_36)), inference(superposition, [status(thm), theory('equality')], [c_65, c_16])).
% 2.02/1.42  tff(c_89, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(resolution, [status(thm)], [c_53, c_86])).
% 2.02/1.42  tff(c_93, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_89])).
% 2.02/1.42  tff(c_95, plain, (k2_mcart_1('#skF_1')='#skF_4'), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.42  tff(c_28, plain, (k1_mcart_1('#skF_1')!='#skF_2' | k2_mcart_1('#skF_1')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.02/1.42  tff(c_101, plain, (k1_mcart_1('#skF_1')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_95, c_28])).
% 2.02/1.42  tff(c_94, plain, (k1_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.02/1.42  tff(c_113, plain, (![A_42, B_43, C_44]: (r2_hidden(k1_mcart_1(A_42), B_43) | ~r2_hidden(A_42, k2_zfmisc_1(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.02/1.42  tff(c_116, plain, (r2_hidden(k1_mcart_1('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_113])).
% 2.02/1.42  tff(c_176, plain, (![A_61, B_62, C_63]: (k4_xboole_0(k1_enumset1(A_61, B_62, C_63), k1_tarski(A_61))=k2_tarski(B_62, C_63) | C_63=A_61 | B_62=A_61)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.02/1.42  tff(c_198, plain, (![A_64, B_65, C_66]: (~r2_hidden(A_64, k2_tarski(B_65, C_66)) | C_66=A_64 | B_65=A_64)), inference(superposition, [status(thm), theory('equality')], [c_176, c_16])).
% 2.02/1.42  tff(c_201, plain, (k1_mcart_1('#skF_1')='#skF_3' | k1_mcart_1('#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_116, c_198])).
% 2.02/1.42  tff(c_208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_101, c_94, c_201])).
% 2.02/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.02/1.42  
% 2.02/1.42  Inference rules
% 2.02/1.42  ----------------------
% 2.02/1.42  #Ref     : 0
% 2.02/1.42  #Sup     : 38
% 2.02/1.42  #Fact    : 0
% 2.02/1.42  #Define  : 0
% 2.02/1.42  #Split   : 1
% 2.02/1.42  #Chain   : 0
% 2.02/1.42  #Close   : 0
% 2.02/1.42  
% 2.02/1.42  Ordering : KBO
% 2.02/1.42  
% 2.02/1.42  Simplification rules
% 2.02/1.42  ----------------------
% 2.02/1.42  #Subsume      : 1
% 2.02/1.42  #Demod        : 2
% 2.02/1.42  #Tautology    : 27
% 2.02/1.42  #SimpNegUnit  : 2
% 2.02/1.42  #BackRed      : 0
% 2.02/1.42  
% 2.02/1.42  #Partial instantiations: 0
% 2.02/1.42  #Strategies tried      : 1
% 2.02/1.42  
% 2.02/1.42  Timing (in seconds)
% 2.02/1.42  ----------------------
% 2.02/1.42  Preprocessing        : 0.36
% 2.02/1.42  Parsing              : 0.18
% 2.02/1.42  CNF conversion       : 0.02
% 2.02/1.42  Main loop            : 0.16
% 2.02/1.42  Inferencing          : 0.06
% 2.02/1.42  Reduction            : 0.04
% 2.02/1.42  Demodulation         : 0.03
% 2.02/1.42  BG Simplification    : 0.01
% 2.02/1.42  Subsumption          : 0.02
% 2.02/1.42  Abstraction          : 0.01
% 2.02/1.42  MUC search           : 0.00
% 2.02/1.42  Cooper               : 0.00
% 2.02/1.42  Total                : 0.54
% 2.02/1.42  Index Insertion      : 0.00
% 2.02/1.42  Index Deletion       : 0.00
% 2.02/1.42  Index Matching       : 0.00
% 2.02/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
