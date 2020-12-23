%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:07 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.38s
% Verified   : 
% Statistics : Number of formulae       :   49 (  69 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 (  91 expanded)
%              Number of equality atoms :   34 (  54 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_280,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k2_tarski(A_51,B_52),C_53)
      | ~ r2_hidden(B_52,C_53)
      | ~ r2_hidden(A_51,C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_5,B_6] :
      ( k4_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_295,plain,(
    ! [A_51,B_52,C_53] :
      ( k4_xboole_0(k2_tarski(A_51,B_52),C_53) = k1_xboole_0
      | ~ r2_hidden(B_52,C_53)
      | ~ r2_hidden(A_51,C_53) ) ),
    inference(resolution,[status(thm)],[c_280,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_78,plain,(
    ! [A_24,B_25] :
      ( k4_xboole_0(A_24,B_25) = k1_xboole_0
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_78])).

tff(c_16,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_178,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k3_xboole_0(A_44,B_45)) = k4_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_44,B_45] : k4_xboole_0(A_44,k4_xboole_0(A_44,B_45)) = k3_xboole_0(A_44,k3_xboole_0(A_44,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_16])).

tff(c_398,plain,(
    ! [A_57,B_58] : k3_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_184])).

tff(c_199,plain,(
    ! [B_2,A_1] : k4_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_178])).

tff(c_407,plain,(
    ! [A_57,B_58] : k4_xboole_0(k3_xboole_0(A_57,B_58),k3_xboole_0(A_57,B_58)) = k4_xboole_0(k3_xboole_0(A_57,B_58),A_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_199])).

tff(c_451,plain,(
    ! [A_59,B_60] : k4_xboole_0(k3_xboole_0(A_59,B_60),A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_407])).

tff(c_476,plain,(
    ! [A_1,B_2] : k4_xboole_0(k3_xboole_0(A_1,B_2),B_2) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_451])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_144,plain,(
    ! [B_32,A_33] :
      ( B_32 = A_33
      | ~ r1_tarski(B_32,A_33)
      | ~ r1_tarski(A_33,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_936,plain,(
    ! [B_76,A_77] :
      ( B_76 = A_77
      | ~ r1_tarski(B_76,A_77)
      | k4_xboole_0(A_77,B_76) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_144])).

tff(c_1474,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | k4_xboole_0(B_91,A_92) != k1_xboole_0
      | k4_xboole_0(A_92,B_91) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_936])).

tff(c_1492,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = B_2
      | k4_xboole_0(B_2,A_1) != k1_xboole_0
      | k4_xboole_0(k3_xboole_0(A_1,B_2),B_2) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_1474])).

tff(c_2200,plain,(
    ! [A_110,B_111] :
      ( k3_xboole_0(A_110,B_111) = B_111
      | k4_xboole_0(B_111,A_110) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_1492])).

tff(c_4697,plain,(
    ! [C_183,A_184,B_185] :
      ( k3_xboole_0(C_183,k2_tarski(A_184,B_185)) = k2_tarski(A_184,B_185)
      | ~ r2_hidden(B_185,C_183)
      | ~ r2_hidden(A_184,C_183) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_295,c_2200])).

tff(c_28,plain,(
    k3_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != k2_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    k3_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_4833,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4697,c_34])).

tff(c_4907,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_4833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:22:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.82  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.82  
% 4.38/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.82  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.38/1.82  
% 4.38/1.82  %Foreground sorts:
% 4.38/1.82  
% 4.38/1.82  
% 4.38/1.82  %Background operators:
% 4.38/1.82  
% 4.38/1.82  
% 4.38/1.82  %Foreground operators:
% 4.38/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.38/1.82  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.38/1.82  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.38/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.38/1.82  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.38/1.82  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.38/1.82  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.38/1.82  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.38/1.82  tff('#skF_2', type, '#skF_2': $i).
% 4.38/1.82  tff('#skF_3', type, '#skF_3': $i).
% 4.38/1.82  tff('#skF_1', type, '#skF_1': $i).
% 4.38/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.38/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.38/1.82  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.38/1.82  
% 4.38/1.83  tff(f_58, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 4.38/1.83  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.38/1.83  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.38/1.83  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.38/1.83  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.38/1.83  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.38/1.83  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 4.38/1.83  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.38/1.83  tff(c_30, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.38/1.83  tff(c_280, plain, (![A_51, B_52, C_53]: (r1_tarski(k2_tarski(A_51, B_52), C_53) | ~r2_hidden(B_52, C_53) | ~r2_hidden(A_51, C_53))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.38/1.83  tff(c_12, plain, (![A_5, B_6]: (k4_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.83  tff(c_295, plain, (![A_51, B_52, C_53]: (k4_xboole_0(k2_tarski(A_51, B_52), C_53)=k1_xboole_0 | ~r2_hidden(B_52, C_53) | ~r2_hidden(A_51, C_53))), inference(resolution, [status(thm)], [c_280, c_12])).
% 4.38/1.83  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.38/1.83  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.83  tff(c_78, plain, (![A_24, B_25]: (k4_xboole_0(A_24, B_25)=k1_xboole_0 | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.83  tff(c_82, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_78])).
% 4.38/1.83  tff(c_16, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.38/1.83  tff(c_178, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k3_xboole_0(A_44, B_45))=k4_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.38/1.83  tff(c_184, plain, (![A_44, B_45]: (k4_xboole_0(A_44, k4_xboole_0(A_44, B_45))=k3_xboole_0(A_44, k3_xboole_0(A_44, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_16])).
% 4.38/1.83  tff(c_398, plain, (![A_57, B_58]: (k3_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k3_xboole_0(A_57, B_58))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_184])).
% 4.38/1.83  tff(c_199, plain, (![B_2, A_1]: (k4_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_178])).
% 4.38/1.83  tff(c_407, plain, (![A_57, B_58]: (k4_xboole_0(k3_xboole_0(A_57, B_58), k3_xboole_0(A_57, B_58))=k4_xboole_0(k3_xboole_0(A_57, B_58), A_57))), inference(superposition, [status(thm), theory('equality')], [c_398, c_199])).
% 4.38/1.83  tff(c_451, plain, (![A_59, B_60]: (k4_xboole_0(k3_xboole_0(A_59, B_60), A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_82, c_407])).
% 4.38/1.83  tff(c_476, plain, (![A_1, B_2]: (k4_xboole_0(k3_xboole_0(A_1, B_2), B_2)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_451])).
% 4.38/1.83  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.38/1.83  tff(c_144, plain, (![B_32, A_33]: (B_32=A_33 | ~r1_tarski(B_32, A_33) | ~r1_tarski(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.38/1.83  tff(c_936, plain, (![B_76, A_77]: (B_76=A_77 | ~r1_tarski(B_76, A_77) | k4_xboole_0(A_77, B_76)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_144])).
% 4.38/1.83  tff(c_1474, plain, (![B_91, A_92]: (B_91=A_92 | k4_xboole_0(B_91, A_92)!=k1_xboole_0 | k4_xboole_0(A_92, B_91)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_936])).
% 4.38/1.83  tff(c_1492, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=B_2 | k4_xboole_0(B_2, A_1)!=k1_xboole_0 | k4_xboole_0(k3_xboole_0(A_1, B_2), B_2)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_199, c_1474])).
% 4.38/1.83  tff(c_2200, plain, (![A_110, B_111]: (k3_xboole_0(A_110, B_111)=B_111 | k4_xboole_0(B_111, A_110)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_476, c_1492])).
% 4.38/1.83  tff(c_4697, plain, (![C_183, A_184, B_185]: (k3_xboole_0(C_183, k2_tarski(A_184, B_185))=k2_tarski(A_184, B_185) | ~r2_hidden(B_185, C_183) | ~r2_hidden(A_184, C_183))), inference(superposition, [status(thm), theory('equality')], [c_295, c_2200])).
% 4.38/1.83  tff(c_28, plain, (k3_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!=k2_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.38/1.83  tff(c_34, plain, (k3_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 4.38/1.83  tff(c_4833, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4697, c_34])).
% 4.38/1.83  tff(c_4907, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_4833])).
% 4.38/1.83  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.38/1.83  
% 4.38/1.83  Inference rules
% 4.38/1.83  ----------------------
% 4.38/1.83  #Ref     : 0
% 4.38/1.83  #Sup     : 1151
% 4.38/1.83  #Fact    : 0
% 4.38/1.83  #Define  : 0
% 4.38/1.83  #Split   : 0
% 4.38/1.83  #Chain   : 0
% 4.38/1.83  #Close   : 0
% 4.38/1.83  
% 4.38/1.83  Ordering : KBO
% 4.38/1.83  
% 4.38/1.83  Simplification rules
% 4.38/1.83  ----------------------
% 4.38/1.83  #Subsume      : 207
% 4.38/1.83  #Demod        : 1565
% 4.38/1.83  #Tautology    : 812
% 4.38/1.83  #SimpNegUnit  : 0
% 4.38/1.83  #BackRed      : 9
% 4.38/1.83  
% 4.38/1.83  #Partial instantiations: 0
% 4.38/1.83  #Strategies tried      : 1
% 4.38/1.83  
% 4.38/1.83  Timing (in seconds)
% 4.38/1.83  ----------------------
% 4.38/1.84  Preprocessing        : 0.28
% 4.38/1.84  Parsing              : 0.15
% 4.38/1.84  CNF conversion       : 0.02
% 4.38/1.84  Main loop            : 0.80
% 4.38/1.84  Inferencing          : 0.24
% 4.38/1.84  Reduction            : 0.39
% 4.38/1.84  Demodulation         : 0.32
% 4.38/1.84  BG Simplification    : 0.02
% 4.38/1.84  Subsumption          : 0.11
% 4.38/1.84  Abstraction          : 0.04
% 4.38/1.84  MUC search           : 0.00
% 4.38/1.84  Cooper               : 0.00
% 4.38/1.84  Total                : 1.11
% 4.38/1.84  Index Insertion      : 0.00
% 4.38/1.84  Index Deletion       : 0.00
% 4.38/1.84  Index Matching       : 0.00
% 4.38/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
