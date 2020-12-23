%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:15 EST 2020

% Result     : Theorem 4.74s
% Output     : CNFRefutation 4.74s
% Verified   : 
% Statistics : Number of formulae       :   50 (  64 expanded)
%              Number of leaves         :   23 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 (  93 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_38,plain,
    ( ~ r1_xboole_0('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_40,plain,(
    r1_tarski('#skF_4',k4_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_34,plain,(
    ! [A_21,B_22] : r1_tarski(k4_xboole_0(A_21,B_22),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_284,plain,(
    ! [A_60,B_61] : k3_xboole_0(k4_xboole_0(A_60,B_61),A_60) = k4_xboole_0(A_60,B_61) ),
    inference(resolution,[status(thm)],[c_34,c_76])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_107,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,B_35)
      | ~ r1_tarski(A_34,k3_xboole_0(B_35,C_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_116,plain,(
    ! [A_34,B_2,A_1] :
      ( r1_tarski(A_34,B_2)
      | ~ r1_tarski(A_34,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_107])).

tff(c_392,plain,(
    ! [A_72,A_73,B_74] :
      ( r1_tarski(A_72,A_73)
      | ~ r1_tarski(A_72,k4_xboole_0(A_73,B_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_284,c_116])).

tff(c_423,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_392])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_423])).

tff(c_436,plain,(
    ~ r1_xboole_0('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_26,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),A_9)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_24,plain,(
    ! [A_9,B_10] :
      ( r2_hidden('#skF_3'(A_9,B_10),B_10)
      | r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_437,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_471,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_481,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_437,c_471])).

tff(c_851,plain,(
    ! [A_120,B_121,C_122] : k4_xboole_0(k3_xboole_0(A_120,B_121),C_122) = k3_xboole_0(A_120,k4_xboole_0(B_121,C_122)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1209,plain,(
    ! [C_139] : k3_xboole_0('#skF_4',k4_xboole_0('#skF_5',C_139)) = k4_xboole_0('#skF_4',C_139) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_851])).

tff(c_483,plain,(
    k3_xboole_0('#skF_4',k4_xboole_0('#skF_5','#skF_6')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_471])).

tff(c_1236,plain,(
    k4_xboole_0('#skF_4','#skF_6') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_483])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1471,plain,(
    ! [D_147] :
      ( ~ r2_hidden(D_147,'#skF_6')
      | ~ r2_hidden(D_147,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_6])).

tff(c_4696,plain,(
    ! [A_226] :
      ( ~ r2_hidden('#skF_3'(A_226,'#skF_6'),'#skF_4')
      | r1_xboole_0(A_226,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_1471])).

tff(c_4700,plain,(
    r1_xboole_0('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_26,c_4696])).

tff(c_4704,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_436,c_4700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:18:19 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.74/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.87  
% 4.74/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.88  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 4.74/1.88  
% 4.74/1.88  %Foreground sorts:
% 4.74/1.88  
% 4.74/1.88  
% 4.74/1.88  %Background operators:
% 4.74/1.88  
% 4.74/1.88  
% 4.74/1.88  %Foreground operators:
% 4.74/1.88  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.74/1.88  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.74/1.88  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.74/1.88  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.74/1.88  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 4.74/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.74/1.88  tff('#skF_5', type, '#skF_5': $i).
% 4.74/1.88  tff('#skF_6', type, '#skF_6': $i).
% 4.74/1.88  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.74/1.88  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.74/1.88  tff('#skF_4', type, '#skF_4': $i).
% 4.74/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.74/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.74/1.88  
% 4.74/1.89  tff(f_76, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.74/1.89  tff(f_67, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.74/1.89  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.74/1.89  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.74/1.89  tff(f_61, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 4.74/1.89  tff(f_55, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.74/1.89  tff(f_69, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 4.74/1.89  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.74/1.89  tff(c_38, plain, (~r1_xboole_0('#skF_4', '#skF_6') | ~r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.74/1.89  tff(c_42, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_38])).
% 4.74/1.89  tff(c_40, plain, (r1_tarski('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.74/1.89  tff(c_34, plain, (![A_21, B_22]: (r1_tarski(k4_xboole_0(A_21, B_22), A_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.74/1.89  tff(c_76, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.89  tff(c_284, plain, (![A_60, B_61]: (k3_xboole_0(k4_xboole_0(A_60, B_61), A_60)=k4_xboole_0(A_60, B_61))), inference(resolution, [status(thm)], [c_34, c_76])).
% 4.74/1.89  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.74/1.89  tff(c_107, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, B_35) | ~r1_tarski(A_34, k3_xboole_0(B_35, C_36)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.74/1.89  tff(c_116, plain, (![A_34, B_2, A_1]: (r1_tarski(A_34, B_2) | ~r1_tarski(A_34, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_107])).
% 4.74/1.89  tff(c_392, plain, (![A_72, A_73, B_74]: (r1_tarski(A_72, A_73) | ~r1_tarski(A_72, k4_xboole_0(A_73, B_74)))), inference(superposition, [status(thm), theory('equality')], [c_284, c_116])).
% 4.74/1.89  tff(c_423, plain, (r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_392])).
% 4.74/1.89  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_423])).
% 4.74/1.89  tff(c_436, plain, (~r1_xboole_0('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_38])).
% 4.74/1.89  tff(c_26, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), A_9) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.89  tff(c_24, plain, (![A_9, B_10]: (r2_hidden('#skF_3'(A_9, B_10), B_10) | r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.74/1.89  tff(c_437, plain, (r1_tarski('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_38])).
% 4.74/1.89  tff(c_471, plain, (![A_77, B_78]: (k3_xboole_0(A_77, B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.74/1.89  tff(c_481, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_437, c_471])).
% 4.74/1.89  tff(c_851, plain, (![A_120, B_121, C_122]: (k4_xboole_0(k3_xboole_0(A_120, B_121), C_122)=k3_xboole_0(A_120, k4_xboole_0(B_121, C_122)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.74/1.89  tff(c_1209, plain, (![C_139]: (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', C_139))=k4_xboole_0('#skF_4', C_139))), inference(superposition, [status(thm), theory('equality')], [c_481, c_851])).
% 4.74/1.89  tff(c_483, plain, (k3_xboole_0('#skF_4', k4_xboole_0('#skF_5', '#skF_6'))='#skF_4'), inference(resolution, [status(thm)], [c_40, c_471])).
% 4.74/1.89  tff(c_1236, plain, (k4_xboole_0('#skF_4', '#skF_6')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_1209, c_483])).
% 4.74/1.89  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.74/1.89  tff(c_1471, plain, (![D_147]: (~r2_hidden(D_147, '#skF_6') | ~r2_hidden(D_147, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1236, c_6])).
% 4.74/1.89  tff(c_4696, plain, (![A_226]: (~r2_hidden('#skF_3'(A_226, '#skF_6'), '#skF_4') | r1_xboole_0(A_226, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_1471])).
% 4.74/1.89  tff(c_4700, plain, (r1_xboole_0('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_26, c_4696])).
% 4.74/1.89  tff(c_4704, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_436, c_4700])).
% 4.74/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.74/1.89  
% 4.74/1.89  Inference rules
% 4.74/1.89  ----------------------
% 4.74/1.89  #Ref     : 0
% 4.74/1.89  #Sup     : 1145
% 4.74/1.89  #Fact    : 0
% 4.74/1.89  #Define  : 0
% 4.74/1.89  #Split   : 2
% 4.74/1.89  #Chain   : 0
% 4.74/1.89  #Close   : 0
% 4.74/1.89  
% 4.74/1.89  Ordering : KBO
% 4.74/1.89  
% 4.74/1.89  Simplification rules
% 4.74/1.89  ----------------------
% 4.74/1.89  #Subsume      : 64
% 4.74/1.89  #Demod        : 857
% 4.74/1.89  #Tautology    : 594
% 4.74/1.89  #SimpNegUnit  : 2
% 4.74/1.89  #BackRed      : 6
% 4.74/1.89  
% 4.74/1.89  #Partial instantiations: 0
% 4.74/1.89  #Strategies tried      : 1
% 4.74/1.89  
% 4.74/1.89  Timing (in seconds)
% 4.74/1.89  ----------------------
% 4.74/1.89  Preprocessing        : 0.30
% 4.74/1.89  Parsing              : 0.15
% 4.74/1.89  CNF conversion       : 0.02
% 4.74/1.89  Main loop            : 0.82
% 4.74/1.89  Inferencing          : 0.26
% 4.74/1.89  Reduction            : 0.34
% 4.74/1.89  Demodulation         : 0.28
% 4.74/1.89  BG Simplification    : 0.03
% 4.74/1.89  Subsumption          : 0.13
% 4.74/1.89  Abstraction          : 0.04
% 4.74/1.89  MUC search           : 0.00
% 4.74/1.89  Cooper               : 0.00
% 4.74/1.89  Total                : 1.15
% 4.74/1.89  Index Insertion      : 0.00
% 4.74/1.89  Index Deletion       : 0.00
% 4.74/1.89  Index Matching       : 0.00
% 4.74/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
