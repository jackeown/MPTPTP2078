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
% DateTime   : Thu Dec  3 09:53:33 EST 2020

% Result     : Theorem 2.52s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   44 (  65 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  83 expanded)
%              Number of equality atoms :   17 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k3_tarski(k3_xboole_0(A,B)),k3_xboole_0(k3_tarski(A),k3_tarski(B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_zfmisc_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k1_xboole_0
      | ~ r1_tarski(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_50,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_175,plain,(
    ! [A_36,B_37] : k4_xboole_0(A_36,k4_xboole_0(A_36,B_37)) = k3_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_210,plain,(
    ! [B_4] : k4_xboole_0(B_4,k1_xboole_0) = k3_xboole_0(B_4,B_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_175])).

tff(c_216,plain,(
    ! [B_38] : k4_xboole_0(B_38,k1_xboole_0) = B_38 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_210])).

tff(c_18,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_222,plain,(
    ! [B_38] : k4_xboole_0(B_38,B_38) = k3_xboole_0(B_38,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_18])).

tff(c_257,plain,(
    ! [B_38] : k3_xboole_0(B_38,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_222])).

tff(c_20,plain,(
    ! [A_14,B_15,C_16] : k4_xboole_0(k3_xboole_0(A_14,B_15),C_16) = k3_xboole_0(A_14,k4_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k3_tarski(A_17),k3_tarski(B_18))
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_191,plain,(
    ! [A_36,B_37] : r1_tarski(k3_xboole_0(A_36,B_37),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_16])).

tff(c_632,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(A_56,k3_xboole_0(B_57,C_58))
      | ~ r1_tarski(A_56,C_58)
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k3_tarski('#skF_1'),k3_tarski('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_659,plain,
    ( ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2'))
    | ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_632,c_24])).

tff(c_1199,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_659])).

tff(c_1202,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_22,c_1199])).

tff(c_1209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_1202])).

tff(c_1210,plain,(
    ~ r1_tarski(k3_tarski(k3_xboole_0('#skF_1','#skF_2')),k3_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_659])).

tff(c_1218,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_1210])).

tff(c_1222,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_1218])).

tff(c_1226,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_50,c_20,c_1222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.52/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.38  
% 2.52/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.38  %$ r1_tarski > k4_xboole_0 > k3_xboole_0 > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.52/1.38  
% 2.52/1.38  %Foreground sorts:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Background operators:
% 2.52/1.38  
% 2.52/1.38  
% 2.52/1.38  %Foreground operators:
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.52/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.52/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.52/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.52/1.38  tff('#skF_2', type, '#skF_2': $i).
% 2.52/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.52/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.52/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.52/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.52/1.38  
% 2.52/1.39  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.52/1.39  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.52/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.52/1.39  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.52/1.39  tff(f_49, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 2.52/1.39  tff(f_53, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_zfmisc_1)).
% 2.52/1.39  tff(f_45, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.52/1.39  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.52/1.39  tff(f_56, negated_conjecture, ~(![A, B]: r1_tarski(k3_tarski(k3_xboole_0(A, B)), k3_xboole_0(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_zfmisc_1)).
% 2.52/1.39  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.39  tff(c_38, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k1_xboole_0 | ~r1_tarski(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.39  tff(c_50, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.52/1.39  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.52/1.39  tff(c_175, plain, (![A_36, B_37]: (k4_xboole_0(A_36, k4_xboole_0(A_36, B_37))=k3_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.39  tff(c_210, plain, (![B_4]: (k4_xboole_0(B_4, k1_xboole_0)=k3_xboole_0(B_4, B_4))), inference(superposition, [status(thm), theory('equality')], [c_50, c_175])).
% 2.52/1.39  tff(c_216, plain, (![B_38]: (k4_xboole_0(B_38, k1_xboole_0)=B_38)), inference(demodulation, [status(thm), theory('equality')], [c_2, c_210])).
% 2.52/1.39  tff(c_18, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.39  tff(c_222, plain, (![B_38]: (k4_xboole_0(B_38, B_38)=k3_xboole_0(B_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_216, c_18])).
% 2.52/1.39  tff(c_257, plain, (![B_38]: (k3_xboole_0(B_38, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_222])).
% 2.52/1.39  tff(c_20, plain, (![A_14, B_15, C_16]: (k4_xboole_0(k3_xboole_0(A_14, B_15), C_16)=k3_xboole_0(A_14, k4_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.52/1.39  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.39  tff(c_22, plain, (![A_17, B_18]: (r1_tarski(k3_tarski(A_17), k3_tarski(B_18)) | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.52/1.39  tff(c_16, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.52/1.39  tff(c_191, plain, (![A_36, B_37]: (r1_tarski(k3_xboole_0(A_36, B_37), A_36))), inference(superposition, [status(thm), theory('equality')], [c_175, c_16])).
% 2.52/1.39  tff(c_632, plain, (![A_56, B_57, C_58]: (r1_tarski(A_56, k3_xboole_0(B_57, C_58)) | ~r1_tarski(A_56, C_58) | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.52/1.39  tff(c_24, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k3_tarski('#skF_1'), k3_tarski('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.52/1.39  tff(c_659, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2')) | ~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_632, c_24])).
% 2.52/1.39  tff(c_1199, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_1'))), inference(splitLeft, [status(thm)], [c_659])).
% 2.52/1.39  tff(c_1202, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_22, c_1199])).
% 2.52/1.39  tff(c_1209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_191, c_1202])).
% 2.52/1.39  tff(c_1210, plain, (~r1_tarski(k3_tarski(k3_xboole_0('#skF_1', '#skF_2')), k3_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_659])).
% 2.52/1.39  tff(c_1218, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_22, c_1210])).
% 2.52/1.39  tff(c_1222, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_1218])).
% 2.52/1.39  tff(c_1226, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_50, c_20, c_1222])).
% 2.52/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.52/1.39  
% 2.52/1.39  Inference rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Ref     : 0
% 2.52/1.39  #Sup     : 285
% 2.52/1.39  #Fact    : 0
% 2.52/1.39  #Define  : 0
% 2.52/1.39  #Split   : 1
% 2.52/1.39  #Chain   : 0
% 2.52/1.39  #Close   : 0
% 2.52/1.39  
% 2.52/1.39  Ordering : KBO
% 2.52/1.39  
% 2.52/1.39  Simplification rules
% 2.52/1.39  ----------------------
% 2.52/1.39  #Subsume      : 8
% 2.52/1.39  #Demod        : 229
% 2.52/1.39  #Tautology    : 209
% 2.52/1.39  #SimpNegUnit  : 0
% 2.52/1.39  #BackRed      : 0
% 2.52/1.39  
% 2.52/1.39  #Partial instantiations: 0
% 2.52/1.39  #Strategies tried      : 1
% 2.52/1.39  
% 2.52/1.39  Timing (in seconds)
% 2.52/1.39  ----------------------
% 2.77/1.40  Preprocessing        : 0.29
% 2.77/1.40  Parsing              : 0.15
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.34
% 2.77/1.40  Inferencing          : 0.13
% 2.77/1.40  Reduction            : 0.12
% 2.77/1.40  Demodulation         : 0.09
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.05
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.65
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
