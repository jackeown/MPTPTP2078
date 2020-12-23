%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   28 (  33 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  45 expanded)
%              Number of equality atoms :    1 (   2 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_45,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_22,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_20,B_21] :
      ( r2_hidden('#skF_1'(A_20,B_21),A_20)
      | r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_9,B_21] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_9),B_21),A_9)
      | r1_tarski(k1_zfmisc_1(A_9),B_21) ) ),
    inference(resolution,[status(thm)],[c_37,c_10])).

tff(c_24,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [A_26,C_27,B_28] :
      ( r1_tarski(A_26,C_27)
      | ~ r1_tarski(B_28,C_27)
      | ~ r1_tarski(A_26,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_62,plain,(
    ! [A_26] :
      ( r1_tarski(A_26,'#skF_5')
      | ~ r1_tarski(A_26,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_56])).

tff(c_12,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [A_18,B_19] :
      ( ~ r2_hidden('#skF_1'(A_18,B_19),B_19)
      | r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_32,A_33] :
      ( r1_tarski(A_32,k1_zfmisc_1(A_33))
      | ~ r1_tarski('#skF_1'(A_32,k1_zfmisc_1(A_33)),A_33) ) ),
    inference(resolution,[status(thm)],[c_12,c_31])).

tff(c_106,plain,(
    ! [A_39] :
      ( r1_tarski(A_39,k1_zfmisc_1('#skF_5'))
      | ~ r1_tarski('#skF_1'(A_39,k1_zfmisc_1('#skF_5')),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_62,c_78])).

tff(c_110,plain,(
    r1_tarski(k1_zfmisc_1('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_47,c_106])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_22,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:12:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.32  
% 1.78/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.32  %$ r2_hidden > r1_tarski > #nlpp > k1_zfmisc_1 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 1.78/1.32  
% 1.78/1.32  %Foreground sorts:
% 1.78/1.32  
% 1.78/1.32  
% 1.78/1.32  %Background operators:
% 1.78/1.32  
% 1.78/1.32  
% 1.78/1.32  %Foreground operators:
% 1.78/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.78/1.32  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.78/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.32  tff('#skF_5', type, '#skF_5': $i).
% 1.78/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.78/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.78/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.78/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.78/1.32  
% 1.78/1.33  tff(f_50, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.78/1.33  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.78/1.33  tff(f_45, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.78/1.33  tff(f_38, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.78/1.33  tff(c_22, plain, (~r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.78/1.33  tff(c_37, plain, (![A_20, B_21]: (r2_hidden('#skF_1'(A_20, B_21), A_20) | r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.33  tff(c_10, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.33  tff(c_47, plain, (![A_9, B_21]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_9), B_21), A_9) | r1_tarski(k1_zfmisc_1(A_9), B_21))), inference(resolution, [status(thm)], [c_37, c_10])).
% 1.78/1.33  tff(c_24, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.78/1.33  tff(c_56, plain, (![A_26, C_27, B_28]: (r1_tarski(A_26, C_27) | ~r1_tarski(B_28, C_27) | ~r1_tarski(A_26, B_28))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.78/1.33  tff(c_62, plain, (![A_26]: (r1_tarski(A_26, '#skF_5') | ~r1_tarski(A_26, '#skF_4'))), inference(resolution, [status(thm)], [c_24, c_56])).
% 1.78/1.33  tff(c_12, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.78/1.33  tff(c_31, plain, (![A_18, B_19]: (~r2_hidden('#skF_1'(A_18, B_19), B_19) | r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.78/1.33  tff(c_78, plain, (![A_32, A_33]: (r1_tarski(A_32, k1_zfmisc_1(A_33)) | ~r1_tarski('#skF_1'(A_32, k1_zfmisc_1(A_33)), A_33))), inference(resolution, [status(thm)], [c_12, c_31])).
% 1.78/1.33  tff(c_106, plain, (![A_39]: (r1_tarski(A_39, k1_zfmisc_1('#skF_5')) | ~r1_tarski('#skF_1'(A_39, k1_zfmisc_1('#skF_5')), '#skF_4'))), inference(resolution, [status(thm)], [c_62, c_78])).
% 1.78/1.33  tff(c_110, plain, (r1_tarski(k1_zfmisc_1('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(resolution, [status(thm)], [c_47, c_106])).
% 1.78/1.33  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_22, c_110])).
% 1.78/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.33  
% 1.78/1.33  Inference rules
% 1.78/1.33  ----------------------
% 1.78/1.33  #Ref     : 0
% 1.78/1.33  #Sup     : 19
% 1.78/1.33  #Fact    : 0
% 1.78/1.33  #Define  : 0
% 1.78/1.33  #Split   : 0
% 1.78/1.33  #Chain   : 0
% 1.78/1.33  #Close   : 0
% 1.78/1.33  
% 1.78/1.33  Ordering : KBO
% 1.78/1.33  
% 1.78/1.33  Simplification rules
% 1.78/1.33  ----------------------
% 1.78/1.33  #Subsume      : 3
% 1.78/1.33  #Demod        : 2
% 1.78/1.33  #Tautology    : 4
% 1.78/1.33  #SimpNegUnit  : 1
% 1.78/1.33  #BackRed      : 0
% 1.78/1.33  
% 1.78/1.33  #Partial instantiations: 0
% 1.78/1.33  #Strategies tried      : 1
% 1.78/1.33  
% 1.78/1.33  Timing (in seconds)
% 1.78/1.33  ----------------------
% 1.78/1.33  Preprocessing        : 0.36
% 1.78/1.33  Parsing              : 0.21
% 1.78/1.33  CNF conversion       : 0.02
% 1.78/1.33  Main loop            : 0.13
% 1.78/1.33  Inferencing          : 0.05
% 1.78/1.33  Reduction            : 0.03
% 1.78/1.33  Demodulation         : 0.02
% 1.78/1.33  BG Simplification    : 0.02
% 1.78/1.33  Subsumption          : 0.03
% 1.78/1.33  Abstraction          : 0.01
% 1.78/1.33  MUC search           : 0.00
% 1.78/1.33  Cooper               : 0.00
% 1.78/1.33  Total                : 0.51
% 1.78/1.33  Index Insertion      : 0.00
% 1.78/1.33  Index Deletion       : 0.00
% 1.78/1.33  Index Matching       : 0.00
% 1.78/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
