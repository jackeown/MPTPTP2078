%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:38 EST 2020

% Result     : Theorem 1.41s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   22 (  27 expanded)
%              Number of leaves         :   12 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   20 (  31 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_36,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
       => r2_hidden(k4_tarski(B,A),k2_zfmisc_1(D,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t107_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(c_10,plain,(
    r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_16,plain,(
    ! [A_9,C_10,B_11,D_12] :
      ( r2_hidden(A_9,C_10)
      | ~ r2_hidden(k4_tarski(A_9,B_11),k2_zfmisc_1(C_10,D_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_16])).

tff(c_11,plain,(
    ! [B_5,D_6,A_7,C_8] :
      ( r2_hidden(B_5,D_6)
      | ~ r2_hidden(k4_tarski(A_7,B_5),k2_zfmisc_1(C_8,D_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_11])).

tff(c_21,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( r2_hidden(k4_tarski(A_13,B_14),k2_zfmisc_1(C_15,D_16))
      | ~ r2_hidden(B_14,D_16)
      | ~ r2_hidden(A_13,C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ~ r2_hidden(k4_tarski('#skF_2','#skF_1'),k2_zfmisc_1('#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | ~ r2_hidden('#skF_2','#skF_4') ),
    inference(resolution,[status(thm)],[c_21,c_8])).

tff(c_35,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_30])).

tff(c_37,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:46:39 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.41/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.09  
% 1.53/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.10  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.53/1.10  
% 1.53/1.10  %Foreground sorts:
% 1.53/1.10  
% 1.53/1.10  
% 1.53/1.10  %Background operators:
% 1.53/1.10  
% 1.53/1.10  
% 1.53/1.10  %Foreground operators:
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.53/1.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.53/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.53/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.53/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.53/1.10  tff('#skF_4', type, '#skF_4': $i).
% 1.53/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.10  
% 1.53/1.11  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) => r2_hidden(k4_tarski(B, A), k2_zfmisc_1(D, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t107_zfmisc_1)).
% 1.53/1.11  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.53/1.11  tff(c_10, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.53/1.11  tff(c_16, plain, (![A_9, C_10, B_11, D_12]: (r2_hidden(A_9, C_10) | ~r2_hidden(k4_tarski(A_9, B_11), k2_zfmisc_1(C_10, D_12)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.11  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.53/1.11  tff(c_11, plain, (![B_5, D_6, A_7, C_8]: (r2_hidden(B_5, D_6) | ~r2_hidden(k4_tarski(A_7, B_5), k2_zfmisc_1(C_8, D_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.11  tff(c_15, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_11])).
% 1.53/1.11  tff(c_21, plain, (![A_13, B_14, C_15, D_16]: (r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)) | ~r2_hidden(B_14, D_16) | ~r2_hidden(A_13, C_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.53/1.11  tff(c_8, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.53/1.11  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_21, c_8])).
% 1.53/1.11  tff(c_35, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15, c_30])).
% 1.53/1.11  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_35])).
% 1.53/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.11  
% 1.53/1.11  Inference rules
% 1.53/1.11  ----------------------
% 1.53/1.11  #Ref     : 0
% 1.53/1.11  #Sup     : 5
% 1.53/1.11  #Fact    : 0
% 1.53/1.11  #Define  : 0
% 1.53/1.11  #Split   : 0
% 1.53/1.11  #Chain   : 0
% 1.53/1.11  #Close   : 0
% 1.53/1.11  
% 1.53/1.11  Ordering : KBO
% 1.53/1.11  
% 1.53/1.11  Simplification rules
% 1.53/1.11  ----------------------
% 1.53/1.11  #Subsume      : 0
% 1.53/1.11  #Demod        : 2
% 1.53/1.11  #Tautology    : 2
% 1.53/1.11  #SimpNegUnit  : 0
% 1.53/1.11  #BackRed      : 0
% 1.53/1.11  
% 1.53/1.11  #Partial instantiations: 0
% 1.53/1.11  #Strategies tried      : 1
% 1.53/1.11  
% 1.53/1.11  Timing (in seconds)
% 1.53/1.11  ----------------------
% 1.53/1.11  Preprocessing        : 0.25
% 1.53/1.11  Parsing              : 0.14
% 1.53/1.11  CNF conversion       : 0.01
% 1.53/1.11  Main loop            : 0.07
% 1.53/1.11  Inferencing          : 0.03
% 1.53/1.11  Reduction            : 0.02
% 1.53/1.11  Demodulation         : 0.02
% 1.53/1.11  BG Simplification    : 0.01
% 1.53/1.11  Subsumption          : 0.01
% 1.53/1.11  Abstraction          : 0.00
% 1.53/1.11  MUC search           : 0.00
% 1.53/1.11  Cooper               : 0.00
% 1.53/1.11  Total                : 0.35
% 1.53/1.11  Index Insertion      : 0.00
% 1.53/1.11  Index Deletion       : 0.00
% 1.53/1.11  Index Matching       : 0.00
% 1.53/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
