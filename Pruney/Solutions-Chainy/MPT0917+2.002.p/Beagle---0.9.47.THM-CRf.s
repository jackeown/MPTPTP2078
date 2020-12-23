%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:14 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   28 (  34 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  48 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_tarski(E,F) )
       => r1_tarski(k3_zfmisc_1(A,C,E),k3_zfmisc_1(B,D,F)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_mcart_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t119_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2,D_4] :
      ( r1_tarski(k2_zfmisc_1(A_1,C_3),k2_zfmisc_1(B_2,D_4))
      | ~ r1_tarski(C_3,D_4)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    r1_tarski('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_4,plain,(
    ! [A_5,B_6,C_7] : k2_zfmisc_1(k2_zfmisc_1(A_5,B_6),C_7) = k3_zfmisc_1(A_5,B_6,C_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_11,C_12,B_13,D_14] :
      ( r1_tarski(k2_zfmisc_1(A_11,C_12),k2_zfmisc_1(B_13,D_14))
      | ~ r1_tarski(C_12,D_14)
      | ~ r1_tarski(A_11,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_49,plain,(
    ! [D_23,C_21,B_20,A_22,B_19] :
      ( r1_tarski(k3_zfmisc_1(A_22,B_20,C_21),k2_zfmisc_1(B_19,D_23))
      | ~ r1_tarski(C_21,D_23)
      | ~ r1_tarski(k2_zfmisc_1(A_22,B_20),B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_28])).

tff(c_65,plain,(
    ! [C_29,C_33,B_32,A_34,A_30,B_31] :
      ( r1_tarski(k3_zfmisc_1(A_30,B_31,C_29),k3_zfmisc_1(A_34,B_32,C_33))
      | ~ r1_tarski(C_29,C_33)
      | ~ r1_tarski(k2_zfmisc_1(A_30,B_31),k2_zfmisc_1(A_34,B_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_49])).

tff(c_6,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_1','#skF_3','#skF_5'),k3_zfmisc_1('#skF_2','#skF_4','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_68,plain,
    ( ~ r1_tarski('#skF_5','#skF_6')
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_65,c_6])).

tff(c_77,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_3'),k2_zfmisc_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_68])).

tff(c_82,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_77])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_82])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:38:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.28  
% 1.86/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.28  %$ r1_tarski > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.86/1.28  
% 1.86/1.28  %Foreground sorts:
% 1.86/1.28  
% 1.86/1.28  
% 1.86/1.28  %Background operators:
% 1.86/1.28  
% 1.86/1.28  
% 1.86/1.28  %Foreground operators:
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.28  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.28  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.28  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.28  
% 1.86/1.29  tff(f_42, negated_conjecture, ~(![A, B, C, D, E, F]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_tarski(E, F)) => r1_tarski(k3_zfmisc_1(A, C, E), k3_zfmisc_1(B, D, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_mcart_1)).
% 1.86/1.29  tff(f_31, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t119_zfmisc_1)).
% 1.86/1.29  tff(f_33, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 1.86/1.29  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.29  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.29  tff(c_2, plain, (![A_1, C_3, B_2, D_4]: (r1_tarski(k2_zfmisc_1(A_1, C_3), k2_zfmisc_1(B_2, D_4)) | ~r1_tarski(C_3, D_4) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.29  tff(c_8, plain, (r1_tarski('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.29  tff(c_4, plain, (![A_5, B_6, C_7]: (k2_zfmisc_1(k2_zfmisc_1(A_5, B_6), C_7)=k3_zfmisc_1(A_5, B_6, C_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.86/1.29  tff(c_28, plain, (![A_11, C_12, B_13, D_14]: (r1_tarski(k2_zfmisc_1(A_11, C_12), k2_zfmisc_1(B_13, D_14)) | ~r1_tarski(C_12, D_14) | ~r1_tarski(A_11, B_13))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.86/1.29  tff(c_49, plain, (![D_23, C_21, B_20, A_22, B_19]: (r1_tarski(k3_zfmisc_1(A_22, B_20, C_21), k2_zfmisc_1(B_19, D_23)) | ~r1_tarski(C_21, D_23) | ~r1_tarski(k2_zfmisc_1(A_22, B_20), B_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_28])).
% 1.86/1.29  tff(c_65, plain, (![C_29, C_33, B_32, A_34, A_30, B_31]: (r1_tarski(k3_zfmisc_1(A_30, B_31, C_29), k3_zfmisc_1(A_34, B_32, C_33)) | ~r1_tarski(C_29, C_33) | ~r1_tarski(k2_zfmisc_1(A_30, B_31), k2_zfmisc_1(A_34, B_32)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_49])).
% 1.86/1.29  tff(c_6, plain, (~r1_tarski(k3_zfmisc_1('#skF_1', '#skF_3', '#skF_5'), k3_zfmisc_1('#skF_2', '#skF_4', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.86/1.29  tff(c_68, plain, (~r1_tarski('#skF_5', '#skF_6') | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_65, c_6])).
% 1.86/1.29  tff(c_77, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_3'), k2_zfmisc_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_68])).
% 1.86/1.29  tff(c_82, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2, c_77])).
% 1.86/1.29  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_82])).
% 1.86/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.29  
% 1.86/1.29  Inference rules
% 1.86/1.29  ----------------------
% 1.86/1.29  #Ref     : 0
% 1.86/1.29  #Sup     : 17
% 1.86/1.29  #Fact    : 0
% 1.86/1.29  #Define  : 0
% 1.86/1.29  #Split   : 0
% 1.86/1.29  #Chain   : 0
% 1.86/1.29  #Close   : 0
% 1.86/1.29  
% 1.86/1.29  Ordering : KBO
% 1.86/1.29  
% 1.86/1.29  Simplification rules
% 1.86/1.29  ----------------------
% 1.86/1.29  #Subsume      : 4
% 1.86/1.29  #Demod        : 10
% 1.86/1.29  #Tautology    : 6
% 1.86/1.29  #SimpNegUnit  : 0
% 1.86/1.29  #BackRed      : 0
% 1.86/1.29  
% 1.86/1.29  #Partial instantiations: 0
% 1.86/1.29  #Strategies tried      : 1
% 1.86/1.29  
% 1.86/1.29  Timing (in seconds)
% 1.86/1.29  ----------------------
% 1.86/1.29  Preprocessing        : 0.31
% 1.86/1.29  Parsing              : 0.18
% 1.86/1.29  CNF conversion       : 0.02
% 1.86/1.29  Main loop            : 0.16
% 1.86/1.29  Inferencing          : 0.08
% 1.86/1.29  Reduction            : 0.04
% 1.86/1.29  Demodulation         : 0.03
% 1.86/1.29  BG Simplification    : 0.01
% 1.86/1.29  Subsumption          : 0.02
% 1.86/1.29  Abstraction          : 0.01
% 1.86/1.29  MUC search           : 0.00
% 1.86/1.29  Cooper               : 0.00
% 1.86/1.29  Total                : 0.49
% 1.86/1.30  Index Insertion      : 0.00
% 1.86/1.30  Index Deletion       : 0.00
% 1.86/1.30  Index Matching       : 0.00
% 1.86/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
