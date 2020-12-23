%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:52 EST 2020

% Result     : Theorem 17.34s
% Output     : CNFRefutation 17.34s
% Verified   : 
% Statistics : Number of formulae       :   46 (  62 expanded)
%              Number of leaves         :   19 (  30 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 119 expanded)
%              Number of equality atoms :    3 (   4 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(A,B)
        & r2_hidden(C,k2_xboole_0(A,B))
        & ~ ( r2_hidden(C,A)
            & ~ r2_hidden(C,B) )
        & ~ ( r2_hidden(C,B)
            & ~ r2_hidden(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_xboole_0)).

tff(c_38,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_98,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_1'(A_28,B_29),A_28)
      | r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_103,plain,(
    ! [A_28] : r1_tarski(A_28,A_28) ),
    inference(resolution,[status(thm)],[c_98,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_42,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_43,plain,(
    r1_tarski('#skF_4',k2_xboole_0('#skF_6','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_42])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_117,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_185,plain,(
    ! [A_51,B_52,B_53] :
      ( r2_hidden('#skF_1'(A_51,B_52),B_53)
      | ~ r1_tarski(A_51,B_53)
      | r1_tarski(A_51,B_52) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_10,plain,(
    ! [D_13,B_9,A_8] :
      ( r2_hidden(D_13,B_9)
      | r2_hidden(D_13,A_8)
      | ~ r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45800,plain,(
    ! [A_781,B_782,B_783,A_784] :
      ( r2_hidden('#skF_1'(A_781,B_782),B_783)
      | r2_hidden('#skF_1'(A_781,B_782),A_784)
      | ~ r1_tarski(A_781,k2_xboole_0(A_784,B_783))
      | r1_tarski(A_781,B_782) ) ),
    inference(resolution,[status(thm)],[c_185,c_10])).

tff(c_46094,plain,(
    ! [B_785] :
      ( r2_hidden('#skF_1'('#skF_4',B_785),'#skF_5')
      | r2_hidden('#skF_1'('#skF_4',B_785),'#skF_6')
      | r1_tarski('#skF_4',B_785) ) ),
    inference(resolution,[status(thm)],[c_43,c_45800])).

tff(c_46154,plain,
    ( r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46094,c_6])).

tff(c_46176,plain,(
    r2_hidden('#skF_1'('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_38,c_46154])).

tff(c_40,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_77,plain,(
    ! [B_21,A_22] :
      ( r1_xboole_0(B_21,A_22)
      | ~ r1_xboole_0(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_80,plain,(
    r1_xboole_0('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_77])).

tff(c_125,plain,(
    ! [A_3,B_4,B_35] :
      ( r2_hidden('#skF_1'(A_3,B_4),B_35)
      | ~ r1_tarski(A_3,B_35)
      | r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_14,plain,(
    ! [D_13,A_8,B_9] :
      ( ~ r2_hidden(D_13,A_8)
      | r2_hidden(D_13,k2_xboole_0(A_8,B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_204,plain,(
    ! [C_54,B_55,A_56] :
      ( ~ r2_hidden(C_54,B_55)
      | ~ r2_hidden(C_54,A_56)
      | ~ r2_hidden(C_54,k2_xboole_0(A_56,B_55))
      | ~ r1_xboole_0(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_229,plain,(
    ! [D_57,B_58,A_59] :
      ( ~ r2_hidden(D_57,B_58)
      | ~ r1_xboole_0(A_59,B_58)
      | ~ r2_hidden(D_57,A_59) ) ),
    inference(resolution,[status(thm)],[c_14,c_204])).

tff(c_33395,plain,(
    ! [A_663,B_664,A_665,B_666] :
      ( ~ r1_xboole_0(A_663,B_664)
      | ~ r2_hidden('#skF_1'(A_665,B_666),A_663)
      | ~ r1_tarski(A_665,B_664)
      | r1_tarski(A_665,B_666) ) ),
    inference(resolution,[status(thm)],[c_125,c_229])).

tff(c_33400,plain,(
    ! [A_665,B_666] :
      ( ~ r2_hidden('#skF_1'(A_665,B_666),'#skF_6')
      | ~ r1_tarski(A_665,'#skF_4')
      | r1_tarski(A_665,B_666) ) ),
    inference(resolution,[status(thm)],[c_80,c_33395])).

tff(c_46179,plain,
    ( ~ r1_tarski('#skF_4','#skF_4')
    | r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_46176,c_33400])).

tff(c_46206,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_46179])).

tff(c_46208,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_46206])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:31:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.34/8.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.34/9.00  
% 17.34/9.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.34/9.00  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 17.34/9.00  
% 17.34/9.00  %Foreground sorts:
% 17.34/9.00  
% 17.34/9.00  
% 17.34/9.00  %Background operators:
% 17.34/9.00  
% 17.34/9.00  
% 17.34/9.00  %Foreground operators:
% 17.34/9.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.34/9.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.34/9.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.34/9.00  tff('#skF_5', type, '#skF_5': $i).
% 17.34/9.00  tff('#skF_6', type, '#skF_6': $i).
% 17.34/9.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 17.34/9.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 17.34/9.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.34/9.00  tff('#skF_4', type, '#skF_4': $i).
% 17.34/9.00  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 17.34/9.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.34/9.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 17.34/9.00  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.34/9.00  
% 17.34/9.01  tff(f_71, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 17.34/9.01  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 17.34/9.01  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 17.34/9.01  tff(f_43, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 17.34/9.01  tff(f_47, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 17.34/9.01  tff(f_64, axiom, (![A, B, C]: ~(((r1_xboole_0(A, B) & r2_hidden(C, k2_xboole_0(A, B))) & ~(r2_hidden(C, A) & ~r2_hidden(C, B))) & ~(r2_hidden(C, B) & ~r2_hidden(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_xboole_0)).
% 17.34/9.01  tff(c_38, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.34/9.01  tff(c_98, plain, (![A_28, B_29]: (r2_hidden('#skF_1'(A_28, B_29), A_28) | r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.34/9.01  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.34/9.01  tff(c_103, plain, (![A_28]: (r1_tarski(A_28, A_28))), inference(resolution, [status(thm)], [c_98, c_6])).
% 17.34/9.01  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.34/9.01  tff(c_42, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.34/9.01  tff(c_43, plain, (r1_tarski('#skF_4', k2_xboole_0('#skF_6', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_42])).
% 17.34/9.01  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.34/9.01  tff(c_117, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_34])).
% 17.34/9.01  tff(c_185, plain, (![A_51, B_52, B_53]: (r2_hidden('#skF_1'(A_51, B_52), B_53) | ~r1_tarski(A_51, B_53) | r1_tarski(A_51, B_52))), inference(resolution, [status(thm)], [c_8, c_117])).
% 17.34/9.01  tff(c_10, plain, (![D_13, B_9, A_8]: (r2_hidden(D_13, B_9) | r2_hidden(D_13, A_8) | ~r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.34/9.01  tff(c_45800, plain, (![A_781, B_782, B_783, A_784]: (r2_hidden('#skF_1'(A_781, B_782), B_783) | r2_hidden('#skF_1'(A_781, B_782), A_784) | ~r1_tarski(A_781, k2_xboole_0(A_784, B_783)) | r1_tarski(A_781, B_782))), inference(resolution, [status(thm)], [c_185, c_10])).
% 17.34/9.01  tff(c_46094, plain, (![B_785]: (r2_hidden('#skF_1'('#skF_4', B_785), '#skF_5') | r2_hidden('#skF_1'('#skF_4', B_785), '#skF_6') | r1_tarski('#skF_4', B_785))), inference(resolution, [status(thm)], [c_43, c_45800])).
% 17.34/9.01  tff(c_46154, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_6') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46094, c_6])).
% 17.34/9.01  tff(c_46176, plain, (r2_hidden('#skF_1'('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_38, c_38, c_46154])).
% 17.34/9.01  tff(c_40, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 17.34/9.01  tff(c_77, plain, (![B_21, A_22]: (r1_xboole_0(B_21, A_22) | ~r1_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.34/9.01  tff(c_80, plain, (r1_xboole_0('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_77])).
% 17.34/9.01  tff(c_125, plain, (![A_3, B_4, B_35]: (r2_hidden('#skF_1'(A_3, B_4), B_35) | ~r1_tarski(A_3, B_35) | r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_8, c_117])).
% 17.34/9.01  tff(c_14, plain, (![D_13, A_8, B_9]: (~r2_hidden(D_13, A_8) | r2_hidden(D_13, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.34/9.01  tff(c_204, plain, (![C_54, B_55, A_56]: (~r2_hidden(C_54, B_55) | ~r2_hidden(C_54, A_56) | ~r2_hidden(C_54, k2_xboole_0(A_56, B_55)) | ~r1_xboole_0(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 17.34/9.01  tff(c_229, plain, (![D_57, B_58, A_59]: (~r2_hidden(D_57, B_58) | ~r1_xboole_0(A_59, B_58) | ~r2_hidden(D_57, A_59))), inference(resolution, [status(thm)], [c_14, c_204])).
% 17.34/9.01  tff(c_33395, plain, (![A_663, B_664, A_665, B_666]: (~r1_xboole_0(A_663, B_664) | ~r2_hidden('#skF_1'(A_665, B_666), A_663) | ~r1_tarski(A_665, B_664) | r1_tarski(A_665, B_666))), inference(resolution, [status(thm)], [c_125, c_229])).
% 17.34/9.01  tff(c_33400, plain, (![A_665, B_666]: (~r2_hidden('#skF_1'(A_665, B_666), '#skF_6') | ~r1_tarski(A_665, '#skF_4') | r1_tarski(A_665, B_666))), inference(resolution, [status(thm)], [c_80, c_33395])).
% 17.34/9.01  tff(c_46179, plain, (~r1_tarski('#skF_4', '#skF_4') | r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_46176, c_33400])).
% 17.34/9.01  tff(c_46206, plain, (r1_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_103, c_46179])).
% 17.34/9.01  tff(c_46208, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_46206])).
% 17.34/9.01  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 17.34/9.01  
% 17.34/9.01  Inference rules
% 17.34/9.01  ----------------------
% 17.34/9.01  #Ref     : 0
% 17.34/9.01  #Sup     : 12003
% 17.34/9.01  #Fact    : 46
% 17.34/9.01  #Define  : 0
% 17.34/9.01  #Split   : 4
% 17.34/9.01  #Chain   : 0
% 17.34/9.01  #Close   : 0
% 17.34/9.01  
% 17.34/9.01  Ordering : KBO
% 17.34/9.01  
% 17.34/9.01  Simplification rules
% 17.34/9.01  ----------------------
% 17.34/9.01  #Subsume      : 2779
% 17.34/9.01  #Demod        : 7339
% 17.34/9.01  #Tautology    : 3292
% 17.34/9.01  #SimpNegUnit  : 5
% 17.34/9.01  #BackRed      : 0
% 17.34/9.01  
% 17.34/9.01  #Partial instantiations: 0
% 17.34/9.01  #Strategies tried      : 1
% 17.34/9.01  
% 17.34/9.01  Timing (in seconds)
% 17.34/9.01  ----------------------
% 17.34/9.01  Preprocessing        : 0.29
% 17.34/9.01  Parsing              : 0.15
% 17.34/9.01  CNF conversion       : 0.02
% 17.34/9.01  Main loop            : 7.97
% 17.34/9.01  Inferencing          : 1.14
% 17.34/9.01  Reduction            : 3.45
% 17.34/9.01  Demodulation         : 3.07
% 17.34/9.01  BG Simplification    : 0.16
% 17.34/9.01  Subsumption          : 2.84
% 17.34/9.01  Abstraction          : 0.21
% 17.34/9.01  MUC search           : 0.00
% 17.34/9.01  Cooper               : 0.00
% 17.34/9.01  Total                : 8.28
% 17.34/9.01  Index Insertion      : 0.00
% 17.34/9.01  Index Deletion       : 0.00
% 17.34/9.01  Index Matching       : 0.00
% 17.34/9.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
