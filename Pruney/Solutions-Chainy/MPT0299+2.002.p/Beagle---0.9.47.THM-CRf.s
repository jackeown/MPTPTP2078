%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:39 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.62s
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t107_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

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
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:34:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.07  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.08  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.51/1.08  
% 1.51/1.08  %Foreground sorts:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Background operators:
% 1.51/1.08  
% 1.51/1.08  
% 1.51/1.08  %Foreground operators:
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.08  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.51/1.08  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.51/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.51/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.08  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.51/1.08  tff('#skF_4', type, '#skF_4': $i).
% 1.51/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.08  
% 1.62/1.09  tff(f_36, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) => r2_hidden(k4_tarski(B, A), k2_zfmisc_1(D, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t107_zfmisc_1)).
% 1.62/1.09  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 1.62/1.09  tff(c_10, plain, (r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.09  tff(c_16, plain, (![A_9, C_10, B_11, D_12]: (r2_hidden(A_9, C_10) | ~r2_hidden(k4_tarski(A_9, B_11), k2_zfmisc_1(C_10, D_12)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.09  tff(c_20, plain, (r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_10, c_16])).
% 1.62/1.09  tff(c_11, plain, (![B_5, D_6, A_7, C_8]: (r2_hidden(B_5, D_6) | ~r2_hidden(k4_tarski(A_7, B_5), k2_zfmisc_1(C_8, D_6)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.09  tff(c_15, plain, (r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_10, c_11])).
% 1.62/1.09  tff(c_21, plain, (![A_13, B_14, C_15, D_16]: (r2_hidden(k4_tarski(A_13, B_14), k2_zfmisc_1(C_15, D_16)) | ~r2_hidden(B_14, D_16) | ~r2_hidden(A_13, C_15))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.09  tff(c_8, plain, (~r2_hidden(k4_tarski('#skF_2', '#skF_1'), k2_zfmisc_1('#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.62/1.09  tff(c_30, plain, (~r2_hidden('#skF_1', '#skF_3') | ~r2_hidden('#skF_2', '#skF_4')), inference(resolution, [status(thm)], [c_21, c_8])).
% 1.62/1.09  tff(c_35, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15, c_30])).
% 1.62/1.09  tff(c_37, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_35])).
% 1.62/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.09  
% 1.62/1.09  Inference rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Ref     : 0
% 1.62/1.09  #Sup     : 5
% 1.62/1.09  #Fact    : 0
% 1.62/1.09  #Define  : 0
% 1.62/1.09  #Split   : 0
% 1.62/1.09  #Chain   : 0
% 1.62/1.09  #Close   : 0
% 1.62/1.09  
% 1.62/1.09  Ordering : KBO
% 1.62/1.09  
% 1.62/1.09  Simplification rules
% 1.62/1.09  ----------------------
% 1.62/1.09  #Subsume      : 0
% 1.62/1.09  #Demod        : 2
% 1.62/1.09  #Tautology    : 2
% 1.62/1.09  #SimpNegUnit  : 0
% 1.62/1.09  #BackRed      : 0
% 1.62/1.09  
% 1.62/1.09  #Partial instantiations: 0
% 1.62/1.09  #Strategies tried      : 1
% 1.62/1.09  
% 1.62/1.09  Timing (in seconds)
% 1.62/1.09  ----------------------
% 1.62/1.09  Preprocessing        : 0.25
% 1.62/1.09  Parsing              : 0.14
% 1.62/1.09  CNF conversion       : 0.02
% 1.62/1.09  Main loop            : 0.08
% 1.62/1.09  Inferencing          : 0.03
% 1.62/1.09  Reduction            : 0.02
% 1.62/1.09  Demodulation         : 0.01
% 1.62/1.09  BG Simplification    : 0.01
% 1.62/1.09  Subsumption          : 0.01
% 1.62/1.09  Abstraction          : 0.00
% 1.62/1.09  MUC search           : 0.00
% 1.62/1.09  Cooper               : 0.00
% 1.62/1.09  Total                : 0.36
% 1.62/1.09  Index Insertion      : 0.00
% 1.62/1.09  Index Deletion       : 0.00
% 1.62/1.09  Index Matching       : 0.00
% 1.62/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------
