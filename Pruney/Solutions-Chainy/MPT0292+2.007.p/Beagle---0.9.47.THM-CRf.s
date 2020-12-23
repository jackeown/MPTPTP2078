%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:35 EST 2020

% Result     : Theorem 2.16s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   38 (  41 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  58 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
         => r1_tarski(C,B) )
     => r1_tarski(k3_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [C_7,A_3] :
      ( r2_hidden(C_7,k1_zfmisc_1(A_3))
      | ~ r1_tarski(C_7,A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_135,plain,(
    ! [A_41,B_42] :
      ( r2_hidden('#skF_3'(A_41,B_42),A_41)
      | r1_tarski(k3_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [C_7,A_3] :
      ( r1_tarski(C_7,A_3)
      | ~ r2_hidden(C_7,k1_zfmisc_1(A_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_389,plain,(
    ! [A_73,B_74] :
      ( r1_tarski('#skF_3'(k1_zfmisc_1(A_73),B_74),A_73)
      | r1_tarski(k3_tarski(k1_zfmisc_1(A_73)),B_74) ) ),
    inference(resolution,[status(thm)],[c_135,c_8])).

tff(c_26,plain,(
    ! [A_11,B_12] :
      ( ~ r1_tarski('#skF_3'(A_11,B_12),B_12)
      | r1_tarski(k3_tarski(A_11),B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_418,plain,(
    ! [A_75] : r1_tarski(k3_tarski(k1_zfmisc_1(A_75)),A_75) ),
    inference(resolution,[status(thm)],[c_389,c_26])).

tff(c_22,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(k1_tarski(A_8),B_9)
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_24,plain,(
    ! [A_10] : k3_tarski(k1_tarski(A_10)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_62,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k3_tarski(A_27),k3_tarski(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_89,plain,(
    ! [A_33,B_34] :
      ( r1_tarski(A_33,k3_tarski(B_34))
      | ~ r1_tarski(k1_tarski(A_33),B_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_62])).

tff(c_100,plain,(
    ! [A_35,B_36] :
      ( r1_tarski(A_35,k3_tarski(B_36))
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_22,c_89])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_115,plain,(
    ! [B_36,A_35] :
      ( k3_tarski(B_36) = A_35
      | ~ r1_tarski(k3_tarski(B_36),A_35)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_436,plain,(
    ! [A_76] :
      ( k3_tarski(k1_zfmisc_1(A_76)) = A_76
      | ~ r2_hidden(A_76,k1_zfmisc_1(A_76)) ) ),
    inference(resolution,[status(thm)],[c_418,c_115])).

tff(c_440,plain,(
    ! [A_3] :
      ( k3_tarski(k1_zfmisc_1(A_3)) = A_3
      | ~ r1_tarski(A_3,A_3) ) ),
    inference(resolution,[status(thm)],[c_10,c_436])).

tff(c_443,plain,(
    ! [A_3] : k3_tarski(k1_zfmisc_1(A_3)) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_440])).

tff(c_32,plain,(
    k3_tarski(k1_zfmisc_1('#skF_4')) != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_451,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:36:53 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.16/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.26  
% 2.16/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.16/1.27  %$ r2_hidden > r1_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.16/1.27  
% 2.16/1.27  %Foreground sorts:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Background operators:
% 2.16/1.27  
% 2.16/1.27  
% 2.16/1.27  %Foreground operators:
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.16/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.16/1.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.16/1.27  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.16/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.16/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.16/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.16/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.16/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.16/1.27  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.16/1.27  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.16/1.27  
% 2.34/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.34/1.28  tff(f_38, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.34/1.28  tff(f_51, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) => r1_tarski(C, B))) => r1_tarski(k3_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_zfmisc_1)).
% 2.34/1.28  tff(f_42, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.34/1.28  tff(f_44, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.34/1.28  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.34/1.28  tff(f_58, negated_conjecture, ~(![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.34/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.28  tff(c_10, plain, (![C_7, A_3]: (r2_hidden(C_7, k1_zfmisc_1(A_3)) | ~r1_tarski(C_7, A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.28  tff(c_135, plain, (![A_41, B_42]: (r2_hidden('#skF_3'(A_41, B_42), A_41) | r1_tarski(k3_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.28  tff(c_8, plain, (![C_7, A_3]: (r1_tarski(C_7, A_3) | ~r2_hidden(C_7, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.34/1.28  tff(c_389, plain, (![A_73, B_74]: (r1_tarski('#skF_3'(k1_zfmisc_1(A_73), B_74), A_73) | r1_tarski(k3_tarski(k1_zfmisc_1(A_73)), B_74))), inference(resolution, [status(thm)], [c_135, c_8])).
% 2.34/1.28  tff(c_26, plain, (![A_11, B_12]: (~r1_tarski('#skF_3'(A_11, B_12), B_12) | r1_tarski(k3_tarski(A_11), B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.28  tff(c_418, plain, (![A_75]: (r1_tarski(k3_tarski(k1_zfmisc_1(A_75)), A_75))), inference(resolution, [status(thm)], [c_389, c_26])).
% 2.34/1.28  tff(c_22, plain, (![A_8, B_9]: (r1_tarski(k1_tarski(A_8), B_9) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.34/1.28  tff(c_24, plain, (![A_10]: (k3_tarski(k1_tarski(A_10))=A_10)), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.34/1.28  tff(c_62, plain, (![A_27, B_28]: (r1_tarski(k3_tarski(A_27), k3_tarski(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.34/1.28  tff(c_89, plain, (![A_33, B_34]: (r1_tarski(A_33, k3_tarski(B_34)) | ~r1_tarski(k1_tarski(A_33), B_34))), inference(superposition, [status(thm), theory('equality')], [c_24, c_62])).
% 2.34/1.28  tff(c_100, plain, (![A_35, B_36]: (r1_tarski(A_35, k3_tarski(B_36)) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_22, c_89])).
% 2.34/1.28  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.34/1.28  tff(c_115, plain, (![B_36, A_35]: (k3_tarski(B_36)=A_35 | ~r1_tarski(k3_tarski(B_36), A_35) | ~r2_hidden(A_35, B_36))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.34/1.28  tff(c_436, plain, (![A_76]: (k3_tarski(k1_zfmisc_1(A_76))=A_76 | ~r2_hidden(A_76, k1_zfmisc_1(A_76)))), inference(resolution, [status(thm)], [c_418, c_115])).
% 2.34/1.28  tff(c_440, plain, (![A_3]: (k3_tarski(k1_zfmisc_1(A_3))=A_3 | ~r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_10, c_436])).
% 2.34/1.28  tff(c_443, plain, (![A_3]: (k3_tarski(k1_zfmisc_1(A_3))=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_440])).
% 2.34/1.28  tff(c_32, plain, (k3_tarski(k1_zfmisc_1('#skF_4'))!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.34/1.28  tff(c_451, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_443, c_32])).
% 2.34/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  Inference rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Ref     : 0
% 2.34/1.28  #Sup     : 80
% 2.34/1.28  #Fact    : 0
% 2.34/1.28  #Define  : 0
% 2.34/1.28  #Split   : 0
% 2.34/1.28  #Chain   : 0
% 2.34/1.28  #Close   : 0
% 2.34/1.28  
% 2.34/1.28  Ordering : KBO
% 2.34/1.28  
% 2.34/1.28  Simplification rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Subsume      : 2
% 2.34/1.28  #Demod        : 33
% 2.34/1.28  #Tautology    : 20
% 2.34/1.28  #SimpNegUnit  : 0
% 2.34/1.28  #BackRed      : 4
% 2.34/1.28  
% 2.34/1.28  #Partial instantiations: 0
% 2.34/1.28  #Strategies tried      : 1
% 2.34/1.28  
% 2.34/1.28  Timing (in seconds)
% 2.34/1.28  ----------------------
% 2.34/1.28  Preprocessing        : 0.27
% 2.34/1.28  Parsing              : 0.14
% 2.34/1.28  CNF conversion       : 0.02
% 2.34/1.28  Main loop            : 0.25
% 2.34/1.28  Inferencing          : 0.10
% 2.34/1.28  Reduction            : 0.06
% 2.34/1.28  Demodulation         : 0.04
% 2.34/1.28  BG Simplification    : 0.01
% 2.34/1.28  Subsumption          : 0.06
% 2.34/1.28  Abstraction          : 0.01
% 2.34/1.28  MUC search           : 0.00
% 2.34/1.28  Cooper               : 0.00
% 2.34/1.28  Total                : 0.54
% 2.34/1.28  Index Insertion      : 0.00
% 2.34/1.28  Index Deletion       : 0.00
% 2.34/1.28  Index Matching       : 0.00
% 2.34/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
