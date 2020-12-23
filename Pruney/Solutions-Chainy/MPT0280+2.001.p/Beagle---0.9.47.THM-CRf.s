%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:24 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   34 (  44 expanded)
%              Number of leaves         :   17 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  47 expanded)
%              Number of equality atoms :    7 (   8 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)),k1_zfmisc_1(k2_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_zfmisc_1)).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_49,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_73,plain,(
    ! [B_22,A_23] : k3_tarski(k2_tarski(B_22,A_23)) = k2_xboole_0(A_23,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_49])).

tff(c_10,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_97,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_112,plain,(
    ! [A_27,B_26] : r1_tarski(A_27,k2_xboole_0(B_26,A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_2])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(k1_zfmisc_1(A_12),k1_zfmisc_1(B_13))
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_147,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(k2_xboole_0(A_30,C_31),B_32)
      | ~ r1_tarski(C_31,B_32)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'),k1_zfmisc_1('#skF_2')),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_157,plain,
    ( ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_147,c_14])).

tff(c_158,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_1'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_157])).

tff(c_161,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_158])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_161])).

tff(c_166,plain,(
    ~ r1_tarski(k1_zfmisc_1('#skF_2'),k1_zfmisc_1(k2_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_157])).

tff(c_170,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_12,c_166])).

tff(c_174,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:13:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.21  
% 1.58/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.22  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 1.58/1.22  
% 1.58/1.22  %Foreground sorts:
% 1.58/1.22  
% 1.58/1.22  
% 1.58/1.22  %Background operators:
% 1.58/1.22  
% 1.58/1.22  
% 1.58/1.22  %Foreground operators:
% 1.58/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.58/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.58/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.58/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.58/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.22  
% 1.58/1.23  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.58/1.23  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.58/1.23  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.58/1.23  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 1.58/1.23  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.58/1.23  tff(f_46, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)), k1_zfmisc_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_zfmisc_1)).
% 1.58/1.23  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.58/1.23  tff(c_49, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.23  tff(c_73, plain, (![B_22, A_23]: (k3_tarski(k2_tarski(B_22, A_23))=k2_xboole_0(A_23, B_22))), inference(superposition, [status(thm), theory('equality')], [c_6, c_49])).
% 1.58/1.23  tff(c_10, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.23  tff(c_97, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 1.58/1.23  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.23  tff(c_112, plain, (![A_27, B_26]: (r1_tarski(A_27, k2_xboole_0(B_26, A_27)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_2])).
% 1.58/1.23  tff(c_12, plain, (![A_12, B_13]: (r1_tarski(k1_zfmisc_1(A_12), k1_zfmisc_1(B_13)) | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.58/1.23  tff(c_147, plain, (![A_30, C_31, B_32]: (r1_tarski(k2_xboole_0(A_30, C_31), B_32) | ~r1_tarski(C_31, B_32) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.58/1.23  tff(c_14, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1('#skF_1'), k1_zfmisc_1('#skF_2')), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.58/1.23  tff(c_157, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_147, c_14])).
% 1.58/1.23  tff(c_158, plain, (~r1_tarski(k1_zfmisc_1('#skF_1'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_157])).
% 1.58/1.23  tff(c_161, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_158])).
% 1.58/1.23  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_161])).
% 1.58/1.23  tff(c_166, plain, (~r1_tarski(k1_zfmisc_1('#skF_2'), k1_zfmisc_1(k2_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_157])).
% 1.58/1.23  tff(c_170, plain, (~r1_tarski('#skF_2', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_12, c_166])).
% 1.58/1.23  tff(c_174, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_170])).
% 1.58/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.23  
% 1.58/1.23  Inference rules
% 1.58/1.23  ----------------------
% 1.58/1.23  #Ref     : 0
% 1.58/1.23  #Sup     : 37
% 1.58/1.23  #Fact    : 0
% 1.58/1.23  #Define  : 0
% 1.58/1.23  #Split   : 1
% 1.58/1.23  #Chain   : 0
% 1.58/1.23  #Close   : 0
% 1.58/1.23  
% 1.58/1.23  Ordering : KBO
% 1.58/1.23  
% 1.58/1.23  Simplification rules
% 1.58/1.23  ----------------------
% 1.58/1.23  #Subsume      : 3
% 1.58/1.23  #Demod        : 8
% 1.58/1.23  #Tautology    : 28
% 1.58/1.23  #SimpNegUnit  : 0
% 1.58/1.23  #BackRed      : 0
% 1.58/1.23  
% 1.58/1.23  #Partial instantiations: 0
% 1.58/1.23  #Strategies tried      : 1
% 1.58/1.23  
% 1.58/1.23  Timing (in seconds)
% 1.58/1.23  ----------------------
% 1.58/1.23  Preprocessing        : 0.31
% 1.58/1.23  Parsing              : 0.18
% 1.58/1.23  CNF conversion       : 0.01
% 1.58/1.23  Main loop            : 0.12
% 1.58/1.23  Inferencing          : 0.05
% 1.58/1.23  Reduction            : 0.04
% 1.58/1.23  Demodulation         : 0.03
% 1.58/1.23  BG Simplification    : 0.01
% 1.58/1.23  Subsumption          : 0.02
% 1.58/1.23  Abstraction          : 0.01
% 1.58/1.23  MUC search           : 0.00
% 1.58/1.23  Cooper               : 0.00
% 1.58/1.23  Total                : 0.46
% 1.58/1.23  Index Insertion      : 0.00
% 1.58/1.23  Index Deletion       : 0.00
% 1.58/1.23  Index Matching       : 0.00
% 1.58/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
