%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:22 EST 2020

% Result     : Theorem 1.81s
% Output     : CNFRefutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :   40 (  48 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  73 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_40,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    ! [C_18,A_14] :
      ( r1_tarski(C_18,A_14)
      | ~ r2_hidden(C_18,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_74,plain,(
    ! [A_14,B_28] :
      ( r1_tarski('#skF_1'(k1_zfmisc_1(A_14),B_28),A_14)
      | r1_tarski(k1_zfmisc_1(A_14),B_28) ) ),
    inference(resolution,[status(thm)],[c_64,c_28])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    ! [C_39,B_40,A_41] :
      ( r2_hidden(C_39,B_40)
      | ~ r2_hidden(C_39,A_41)
      | ~ r1_tarski(A_41,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_222,plain,(
    ! [A_57,B_58,B_59] :
      ( r2_hidden('#skF_1'(A_57,B_58),B_59)
      | ~ r1_tarski(A_57,B_59)
      | r1_tarski(A_57,B_58) ) ),
    inference(resolution,[status(thm)],[c_6,c_126])).

tff(c_42,plain,(
    r1_tarski('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_48,plain,(
    k3_xboole_0('#skF_6','#skF_7') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_42,c_44])).

tff(c_80,plain,(
    ! [D_30,B_31,A_32] :
      ( r2_hidden(D_30,B_31)
      | ~ r2_hidden(D_30,k3_xboole_0(A_32,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [D_34] :
      ( r2_hidden(D_34,'#skF_7')
      | ~ r2_hidden(D_34,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_80])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_106,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_7')
      | ~ r2_hidden('#skF_1'(A_1,'#skF_7'),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_101,c_4])).

tff(c_255,plain,(
    ! [A_60] :
      ( ~ r1_tarski(A_60,'#skF_6')
      | r1_tarski(A_60,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_222,c_106])).

tff(c_30,plain,(
    ! [C_18,A_14] :
      ( r2_hidden(C_18,k1_zfmisc_1(A_14))
      | ~ r1_tarski(C_18,A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_58,plain,(
    ! [A_25,B_26] :
      ( ~ r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_63,plain,(
    ! [A_25,A_14] :
      ( r1_tarski(A_25,k1_zfmisc_1(A_14))
      | ~ r1_tarski('#skF_1'(A_25,k1_zfmisc_1(A_14)),A_14) ) ),
    inference(resolution,[status(thm)],[c_30,c_58])).

tff(c_293,plain,(
    ! [A_64] :
      ( r1_tarski(A_64,k1_zfmisc_1('#skF_7'))
      | ~ r1_tarski('#skF_1'(A_64,k1_zfmisc_1('#skF_7')),'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_255,c_63])).

tff(c_297,plain,(
    r1_tarski(k1_zfmisc_1('#skF_6'),k1_zfmisc_1('#skF_7')) ),
    inference(resolution,[status(thm)],[c_74,c_293])).

tff(c_301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_297])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n007.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:32:06 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.81/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.25  
% 1.81/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.26  %$ r2_hidden > r1_tarski > k3_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 1.81/1.26  
% 1.81/1.26  %Foreground sorts:
% 1.81/1.26  
% 1.81/1.26  
% 1.81/1.26  %Background operators:
% 1.81/1.26  
% 1.81/1.26  
% 1.81/1.26  %Foreground operators:
% 1.81/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.81/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.81/1.26  tff('#skF_7', type, '#skF_7': $i).
% 1.81/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.81/1.26  tff('#skF_6', type, '#skF_6': $i).
% 1.81/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.81/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.81/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.81/1.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.81/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.81/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.81/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.81/1.26  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.81/1.26  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.81/1.26  
% 1.81/1.27  tff(f_57, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.81/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.81/1.27  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.81/1.27  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.81/1.27  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.81/1.27  tff(c_40, plain, (~r1_tarski(k1_zfmisc_1('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.27  tff(c_64, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.27  tff(c_28, plain, (![C_18, A_14]: (r1_tarski(C_18, A_14) | ~r2_hidden(C_18, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.27  tff(c_74, plain, (![A_14, B_28]: (r1_tarski('#skF_1'(k1_zfmisc_1(A_14), B_28), A_14) | r1_tarski(k1_zfmisc_1(A_14), B_28))), inference(resolution, [status(thm)], [c_64, c_28])).
% 1.81/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.27  tff(c_126, plain, (![C_39, B_40, A_41]: (r2_hidden(C_39, B_40) | ~r2_hidden(C_39, A_41) | ~r1_tarski(A_41, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.27  tff(c_222, plain, (![A_57, B_58, B_59]: (r2_hidden('#skF_1'(A_57, B_58), B_59) | ~r1_tarski(A_57, B_59) | r1_tarski(A_57, B_58))), inference(resolution, [status(thm)], [c_6, c_126])).
% 1.81/1.27  tff(c_42, plain, (r1_tarski('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.81/1.27  tff(c_44, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.81/1.27  tff(c_48, plain, (k3_xboole_0('#skF_6', '#skF_7')='#skF_6'), inference(resolution, [status(thm)], [c_42, c_44])).
% 1.81/1.27  tff(c_80, plain, (![D_30, B_31, A_32]: (r2_hidden(D_30, B_31) | ~r2_hidden(D_30, k3_xboole_0(A_32, B_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.81/1.27  tff(c_101, plain, (![D_34]: (r2_hidden(D_34, '#skF_7') | ~r2_hidden(D_34, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_80])).
% 1.81/1.27  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.27  tff(c_106, plain, (![A_1]: (r1_tarski(A_1, '#skF_7') | ~r2_hidden('#skF_1'(A_1, '#skF_7'), '#skF_6'))), inference(resolution, [status(thm)], [c_101, c_4])).
% 1.81/1.27  tff(c_255, plain, (![A_60]: (~r1_tarski(A_60, '#skF_6') | r1_tarski(A_60, '#skF_7'))), inference(resolution, [status(thm)], [c_222, c_106])).
% 1.81/1.27  tff(c_30, plain, (![C_18, A_14]: (r2_hidden(C_18, k1_zfmisc_1(A_14)) | ~r1_tarski(C_18, A_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.81/1.27  tff(c_58, plain, (![A_25, B_26]: (~r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.81/1.27  tff(c_63, plain, (![A_25, A_14]: (r1_tarski(A_25, k1_zfmisc_1(A_14)) | ~r1_tarski('#skF_1'(A_25, k1_zfmisc_1(A_14)), A_14))), inference(resolution, [status(thm)], [c_30, c_58])).
% 1.81/1.27  tff(c_293, plain, (![A_64]: (r1_tarski(A_64, k1_zfmisc_1('#skF_7')) | ~r1_tarski('#skF_1'(A_64, k1_zfmisc_1('#skF_7')), '#skF_6'))), inference(resolution, [status(thm)], [c_255, c_63])).
% 1.81/1.27  tff(c_297, plain, (r1_tarski(k1_zfmisc_1('#skF_6'), k1_zfmisc_1('#skF_7'))), inference(resolution, [status(thm)], [c_74, c_293])).
% 1.81/1.27  tff(c_301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_297])).
% 1.81/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.27  
% 1.81/1.27  Inference rules
% 1.81/1.27  ----------------------
% 1.81/1.27  #Ref     : 0
% 1.81/1.27  #Sup     : 54
% 1.81/1.27  #Fact    : 0
% 1.81/1.27  #Define  : 0
% 1.81/1.27  #Split   : 0
% 1.81/1.27  #Chain   : 0
% 1.81/1.27  #Close   : 0
% 1.81/1.27  
% 1.81/1.27  Ordering : KBO
% 1.81/1.27  
% 1.81/1.27  Simplification rules
% 1.81/1.27  ----------------------
% 1.81/1.27  #Subsume      : 2
% 1.81/1.27  #Demod        : 6
% 1.81/1.27  #Tautology    : 19
% 1.81/1.27  #SimpNegUnit  : 1
% 1.81/1.27  #BackRed      : 0
% 1.81/1.27  
% 1.81/1.27  #Partial instantiations: 0
% 1.81/1.27  #Strategies tried      : 1
% 1.81/1.27  
% 1.81/1.27  Timing (in seconds)
% 1.81/1.27  ----------------------
% 1.81/1.27  Preprocessing        : 0.29
% 1.81/1.27  Parsing              : 0.16
% 1.81/1.27  CNF conversion       : 0.02
% 1.81/1.27  Main loop            : 0.19
% 1.81/1.27  Inferencing          : 0.08
% 1.81/1.27  Reduction            : 0.05
% 1.81/1.27  Demodulation         : 0.03
% 1.81/1.27  BG Simplification    : 0.02
% 1.81/1.27  Subsumption          : 0.04
% 1.81/1.27  Abstraction          : 0.01
% 1.81/1.27  MUC search           : 0.00
% 1.81/1.27  Cooper               : 0.00
% 1.81/1.27  Total                : 0.51
% 1.81/1.27  Index Insertion      : 0.00
% 1.81/1.27  Index Deletion       : 0.00
% 1.81/1.27  Index Matching       : 0.00
% 1.81/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
