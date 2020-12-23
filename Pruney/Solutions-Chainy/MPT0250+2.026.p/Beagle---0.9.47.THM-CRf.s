%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:35 EST 2020

% Result     : Theorem 3.00s
% Output     : CNFRefutation 3.21s
% Verified   : 
% Statistics : Number of formulae       :   51 (  59 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  68 expanded)
%              Number of equality atoms :   19 (  26 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_64,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_50,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_73,plain,(
    ! [D_34,B_35] : r2_hidden(D_34,k2_tarski(D_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_76,plain,(
    ! [A_22] : r2_hidden(A_22,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_73])).

tff(c_58,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_141,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_184,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_141])).

tff(c_56,plain,(
    ! [A_28,B_29] : k3_tarski(k2_tarski(A_28,B_29)) = k2_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_190,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_56])).

tff(c_60,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_211,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_60])).

tff(c_267,plain,(
    ! [B_59,A_60] :
      ( B_59 = A_60
      | ~ r1_tarski(B_59,A_60)
      | ~ r1_tarski(A_60,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_269,plain,
    ( k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6'
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_6',k1_tarski('#skF_5'))) ),
    inference(resolution,[status(thm)],[c_211,c_267])).

tff(c_280,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_269])).

tff(c_379,plain,(
    ! [A_75,B_76,C_77] : k4_xboole_0(k4_xboole_0(A_75,B_76),C_77) = k4_xboole_0(A_75,k2_xboole_0(B_76,C_77)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_465,plain,(
    ! [D_89,C_90,A_91,B_92] :
      ( ~ r2_hidden(D_89,C_90)
      | ~ r2_hidden(D_89,k4_xboole_0(A_91,k2_xboole_0(B_92,C_90))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_4])).

tff(c_493,plain,(
    ! [D_96,A_97] :
      ( ~ r2_hidden(D_96,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_96,k4_xboole_0(A_97,'#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_465])).

tff(c_538,plain,(
    ! [D_105,A_106] :
      ( ~ r2_hidden(D_105,k1_tarski('#skF_5'))
      | r2_hidden(D_105,'#skF_6')
      | ~ r2_hidden(D_105,A_106) ) ),
    inference(resolution,[status(thm)],[c_2,c_493])).

tff(c_541,plain,(
    ! [A_106] :
      ( r2_hidden('#skF_5','#skF_6')
      | ~ r2_hidden('#skF_5',A_106) ) ),
    inference(resolution,[status(thm)],[c_76,c_538])).

tff(c_545,plain,(
    ! [A_107] : ~ r2_hidden('#skF_5',A_107) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_541])).

tff(c_562,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_76,c_545])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:57:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.00/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.82  
% 3.12/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.83  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 3.12/1.83  
% 3.12/1.83  %Foreground sorts:
% 3.12/1.83  
% 3.12/1.83  
% 3.12/1.83  %Background operators:
% 3.12/1.83  
% 3.12/1.83  
% 3.12/1.83  %Foreground operators:
% 3.12/1.83  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.12/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.12/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.12/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.12/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.12/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.12/1.83  tff('#skF_5', type, '#skF_5': $i).
% 3.12/1.83  tff('#skF_6', type, '#skF_6': $i).
% 3.12/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.12/1.83  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.12/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.83  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.12/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.12/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.83  
% 3.21/1.85  tff(f_58, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.21/1.85  tff(f_56, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.21/1.85  tff(f_69, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 3.21/1.85  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.21/1.85  tff(f_45, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.21/1.85  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.21/1.85  tff(f_64, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.21/1.85  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.21/1.85  tff(f_43, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 3.21/1.85  tff(c_50, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.21/1.85  tff(c_73, plain, (![D_34, B_35]: (r2_hidden(D_34, k2_tarski(D_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.21/1.85  tff(c_76, plain, (![A_22]: (r2_hidden(A_22, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_73])).
% 3.21/1.85  tff(c_58, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.85  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.85  tff(c_28, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.21/1.85  tff(c_30, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.21/1.85  tff(c_141, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.21/1.85  tff(c_184, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_30, c_141])).
% 3.21/1.85  tff(c_56, plain, (![A_28, B_29]: (k3_tarski(k2_tarski(A_28, B_29))=k2_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.21/1.85  tff(c_190, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_184, c_56])).
% 3.21/1.85  tff(c_60, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.21/1.85  tff(c_211, plain, (r1_tarski(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_190, c_60])).
% 3.21/1.85  tff(c_267, plain, (![B_59, A_60]: (B_59=A_60 | ~r1_tarski(B_59, A_60) | ~r1_tarski(A_60, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.21/1.85  tff(c_269, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6' | ~r1_tarski('#skF_6', k2_xboole_0('#skF_6', k1_tarski('#skF_5')))), inference(resolution, [status(thm)], [c_211, c_267])).
% 3.21/1.85  tff(c_280, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_269])).
% 3.21/1.85  tff(c_379, plain, (![A_75, B_76, C_77]: (k4_xboole_0(k4_xboole_0(A_75, B_76), C_77)=k4_xboole_0(A_75, k2_xboole_0(B_76, C_77)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.21/1.85  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.21/1.85  tff(c_465, plain, (![D_89, C_90, A_91, B_92]: (~r2_hidden(D_89, C_90) | ~r2_hidden(D_89, k4_xboole_0(A_91, k2_xboole_0(B_92, C_90))))), inference(superposition, [status(thm), theory('equality')], [c_379, c_4])).
% 3.21/1.85  tff(c_493, plain, (![D_96, A_97]: (~r2_hidden(D_96, k1_tarski('#skF_5')) | ~r2_hidden(D_96, k4_xboole_0(A_97, '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_280, c_465])).
% 3.21/1.85  tff(c_538, plain, (![D_105, A_106]: (~r2_hidden(D_105, k1_tarski('#skF_5')) | r2_hidden(D_105, '#skF_6') | ~r2_hidden(D_105, A_106))), inference(resolution, [status(thm)], [c_2, c_493])).
% 3.21/1.85  tff(c_541, plain, (![A_106]: (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_5', A_106))), inference(resolution, [status(thm)], [c_76, c_538])).
% 3.21/1.85  tff(c_545, plain, (![A_107]: (~r2_hidden('#skF_5', A_107))), inference(negUnitSimplification, [status(thm)], [c_58, c_541])).
% 3.21/1.85  tff(c_562, plain, $false, inference(resolution, [status(thm)], [c_76, c_545])).
% 3.21/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.21/1.85  
% 3.21/1.85  Inference rules
% 3.21/1.85  ----------------------
% 3.21/1.85  #Ref     : 0
% 3.21/1.85  #Sup     : 123
% 3.21/1.85  #Fact    : 0
% 3.21/1.85  #Define  : 0
% 3.21/1.85  #Split   : 1
% 3.21/1.85  #Chain   : 0
% 3.21/1.85  #Close   : 0
% 3.21/1.85  
% 3.21/1.85  Ordering : KBO
% 3.21/1.85  
% 3.21/1.85  Simplification rules
% 3.21/1.85  ----------------------
% 3.21/1.85  #Subsume      : 26
% 3.21/1.85  #Demod        : 32
% 3.21/1.85  #Tautology    : 60
% 3.21/1.85  #SimpNegUnit  : 2
% 3.21/1.85  #BackRed      : 2
% 3.21/1.85  
% 3.21/1.85  #Partial instantiations: 0
% 3.21/1.85  #Strategies tried      : 1
% 3.21/1.85  
% 3.21/1.85  Timing (in seconds)
% 3.21/1.85  ----------------------
% 3.21/1.85  Preprocessing        : 0.49
% 3.21/1.85  Parsing              : 0.23
% 3.21/1.85  CNF conversion       : 0.04
% 3.21/1.85  Main loop            : 0.45
% 3.21/1.85  Inferencing          : 0.14
% 3.21/1.85  Reduction            : 0.17
% 3.21/1.85  Demodulation         : 0.14
% 3.21/1.85  BG Simplification    : 0.03
% 3.21/1.85  Subsumption          : 0.09
% 3.21/1.85  Abstraction          : 0.03
% 3.21/1.85  MUC search           : 0.00
% 3.21/1.85  Cooper               : 0.00
% 3.21/1.85  Total                : 0.98
% 3.21/1.86  Index Insertion      : 0.00
% 3.21/1.86  Index Deletion       : 0.00
% 3.21/1.86  Index Matching       : 0.00
% 3.21/1.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
