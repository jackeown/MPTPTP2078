%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 4.09s
% Output     : CNFRefutation 4.09s
% Verified   : 
% Statistics : Number of formulae       :   52 (  58 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   52 (  63 expanded)
%              Number of equality atoms :   26 (  30 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_36,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_11,B_12] : r1_tarski(A_11,k2_xboole_0(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_71,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_71])).

tff(c_83,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_87,plain,(
    ! [A_11,B_12] : k3_xboole_0(A_11,k2_xboole_0(A_11,B_12)) = A_11 ),
    inference(resolution,[status(thm)],[c_14,c_83])).

tff(c_222,plain,(
    ! [A_53,B_54] : k2_xboole_0(k3_xboole_0(A_53,B_54),k4_xboole_0(A_53,B_54)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_243,plain,(
    ! [A_11,B_12] : k2_xboole_0(A_11,k4_xboole_0(A_11,k2_xboole_0(A_11,B_12))) = A_11 ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_222])).

tff(c_249,plain,(
    ! [A_11] : k2_xboole_0(A_11,k1_xboole_0) = A_11 ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_243])).

tff(c_838,plain,(
    ! [A_95,B_96,C_97] :
      ( r1_tarski(k2_tarski(A_95,B_96),C_97)
      | ~ r2_hidden(B_96,C_97)
      | ~ r2_hidden(A_95,C_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2959,plain,(
    ! [A_156,B_157,C_158] :
      ( k4_xboole_0(k2_tarski(A_156,B_157),C_158) = k1_xboole_0
      | ~ r2_hidden(B_157,C_158)
      | ~ r2_hidden(A_156,C_158) ) ),
    inference(resolution,[status(thm)],[c_838,c_4])).

tff(c_10,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_3003,plain,(
    ! [C_158,A_156,B_157] :
      ( k2_xboole_0(C_158,k2_tarski(A_156,B_157)) = k2_xboole_0(C_158,k1_xboole_0)
      | ~ r2_hidden(B_157,C_158)
      | ~ r2_hidden(A_156,C_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2959,c_10])).

tff(c_4628,plain,(
    ! [C_178,A_179,B_180] :
      ( k2_xboole_0(C_178,k2_tarski(A_179,B_180)) = C_178
      | ~ r2_hidden(B_180,C_178)
      | ~ r2_hidden(A_179,C_178) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_3003])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_106,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_130,plain,(
    ! [B_47,A_48] : k3_tarski(k2_tarski(B_47,A_48)) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_106])).

tff(c_24,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_136,plain,(
    ! [B_47,A_48] : k2_xboole_0(B_47,A_48) = k2_xboole_0(A_48,B_47) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_24])).

tff(c_32,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_153,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_32])).

tff(c_4737,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4628,c_153])).

tff(c_4834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_4737])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:56:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.09/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.79  
% 4.09/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.79  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.09/1.79  
% 4.09/1.79  %Foreground sorts:
% 4.09/1.79  
% 4.09/1.79  
% 4.09/1.79  %Background operators:
% 4.09/1.79  
% 4.09/1.79  
% 4.09/1.79  %Foreground operators:
% 4.09/1.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.09/1.79  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.09/1.79  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.09/1.79  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.09/1.79  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.09/1.79  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.09/1.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.09/1.79  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.09/1.79  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.09/1.79  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.09/1.79  tff('#skF_2', type, '#skF_2': $i).
% 4.09/1.79  tff('#skF_3', type, '#skF_3': $i).
% 4.09/1.79  tff('#skF_1', type, '#skF_1': $i).
% 4.09/1.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.09/1.79  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.09/1.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.09/1.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.09/1.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.09/1.79  
% 4.09/1.81  tff(f_64, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 4.09/1.81  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.09/1.81  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.09/1.81  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.09/1.81  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.09/1.81  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.09/1.81  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 4.09/1.81  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.09/1.81  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.09/1.81  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.09/1.81  tff(c_34, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.09/1.81  tff(c_14, plain, (![A_11, B_12]: (r1_tarski(A_11, k2_xboole_0(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.09/1.81  tff(c_71, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.81  tff(c_75, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k2_xboole_0(A_11, B_12))=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_71])).
% 4.09/1.81  tff(c_83, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.09/1.81  tff(c_87, plain, (![A_11, B_12]: (k3_xboole_0(A_11, k2_xboole_0(A_11, B_12))=A_11)), inference(resolution, [status(thm)], [c_14, c_83])).
% 4.09/1.81  tff(c_222, plain, (![A_53, B_54]: (k2_xboole_0(k3_xboole_0(A_53, B_54), k4_xboole_0(A_53, B_54))=A_53)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.09/1.81  tff(c_243, plain, (![A_11, B_12]: (k2_xboole_0(A_11, k4_xboole_0(A_11, k2_xboole_0(A_11, B_12)))=A_11)), inference(superposition, [status(thm), theory('equality')], [c_87, c_222])).
% 4.09/1.81  tff(c_249, plain, (![A_11]: (k2_xboole_0(A_11, k1_xboole_0)=A_11)), inference(demodulation, [status(thm), theory('equality')], [c_75, c_243])).
% 4.09/1.81  tff(c_838, plain, (![A_95, B_96, C_97]: (r1_tarski(k2_tarski(A_95, B_96), C_97) | ~r2_hidden(B_96, C_97) | ~r2_hidden(A_95, C_97))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.09/1.81  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.09/1.81  tff(c_2959, plain, (![A_156, B_157, C_158]: (k4_xboole_0(k2_tarski(A_156, B_157), C_158)=k1_xboole_0 | ~r2_hidden(B_157, C_158) | ~r2_hidden(A_156, C_158))), inference(resolution, [status(thm)], [c_838, c_4])).
% 4.09/1.81  tff(c_10, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.09/1.81  tff(c_3003, plain, (![C_158, A_156, B_157]: (k2_xboole_0(C_158, k2_tarski(A_156, B_157))=k2_xboole_0(C_158, k1_xboole_0) | ~r2_hidden(B_157, C_158) | ~r2_hidden(A_156, C_158))), inference(superposition, [status(thm), theory('equality')], [c_2959, c_10])).
% 4.09/1.81  tff(c_4628, plain, (![C_178, A_179, B_180]: (k2_xboole_0(C_178, k2_tarski(A_179, B_180))=C_178 | ~r2_hidden(B_180, C_178) | ~r2_hidden(A_179, C_178))), inference(demodulation, [status(thm), theory('equality')], [c_249, c_3003])).
% 4.09/1.81  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.09/1.81  tff(c_106, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.81  tff(c_130, plain, (![B_47, A_48]: (k3_tarski(k2_tarski(B_47, A_48))=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_16, c_106])).
% 4.09/1.81  tff(c_24, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.09/1.81  tff(c_136, plain, (![B_47, A_48]: (k2_xboole_0(B_47, A_48)=k2_xboole_0(A_48, B_47))), inference(superposition, [status(thm), theory('equality')], [c_130, c_24])).
% 4.09/1.81  tff(c_32, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.09/1.81  tff(c_153, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_136, c_32])).
% 4.09/1.81  tff(c_4737, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4628, c_153])).
% 4.09/1.81  tff(c_4834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_4737])).
% 4.09/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.09/1.81  
% 4.09/1.81  Inference rules
% 4.09/1.81  ----------------------
% 4.09/1.81  #Ref     : 0
% 4.09/1.81  #Sup     : 1153
% 4.09/1.81  #Fact    : 0
% 4.09/1.81  #Define  : 0
% 4.09/1.81  #Split   : 0
% 4.09/1.81  #Chain   : 0
% 4.09/1.81  #Close   : 0
% 4.09/1.81  
% 4.09/1.81  Ordering : KBO
% 4.09/1.81  
% 4.09/1.81  Simplification rules
% 4.09/1.81  ----------------------
% 4.09/1.81  #Subsume      : 49
% 4.09/1.81  #Demod        : 1278
% 4.09/1.81  #Tautology    : 928
% 4.09/1.81  #SimpNegUnit  : 0
% 4.09/1.81  #BackRed      : 1
% 4.09/1.81  
% 4.09/1.81  #Partial instantiations: 0
% 4.09/1.81  #Strategies tried      : 1
% 4.09/1.81  
% 4.09/1.81  Timing (in seconds)
% 4.09/1.81  ----------------------
% 4.09/1.81  Preprocessing        : 0.32
% 4.09/1.81  Parsing              : 0.17
% 4.09/1.81  CNF conversion       : 0.02
% 4.09/1.81  Main loop            : 0.69
% 4.09/1.81  Inferencing          : 0.21
% 4.09/1.81  Reduction            : 0.33
% 4.09/1.81  Demodulation         : 0.28
% 4.09/1.81  BG Simplification    : 0.02
% 4.09/1.81  Subsumption          : 0.08
% 4.09/1.81  Abstraction          : 0.04
% 4.09/1.81  MUC search           : 0.00
% 4.09/1.81  Cooper               : 0.00
% 4.09/1.81  Total                : 1.03
% 4.09/1.81  Index Insertion      : 0.00
% 4.09/1.81  Index Deletion       : 0.00
% 4.09/1.81  Index Matching       : 0.00
% 4.09/1.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
