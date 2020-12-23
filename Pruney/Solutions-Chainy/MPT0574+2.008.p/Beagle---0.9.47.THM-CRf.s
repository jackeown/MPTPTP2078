%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:51 EST 2020

% Result     : Theorem 2.58s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   19 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 (  75 expanded)
%              Number of equality atoms :   18 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_59,plain,(
    ! [A_20,B_21] : k3_tarski(k2_tarski(A_20,B_21)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    ! [B_22,A_23] : k3_tarski(k2_tarski(B_22,A_23)) = k2_xboole_0(A_23,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_59])).

tff(c_14,plain,(
    ! [A_10,B_11] : k3_tarski(k2_tarski(A_10,B_11)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    ! [B_22,A_23] : k2_xboole_0(B_22,A_23) = k2_xboole_0(A_23,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_14])).

tff(c_20,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k2_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [B_26,A_27] :
      ( B_26 = A_27
      | ~ r1_tarski(B_26,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_174,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = A_33
      | ~ r1_tarski(k2_xboole_0(A_33,B_34),A_33) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_178,plain,(
    ! [B_6,C_7] :
      ( k2_xboole_0(B_6,C_7) = B_6
      | ~ r1_tarski(C_7,B_6)
      | ~ r1_tarski(B_6,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_174])).

tff(c_188,plain,(
    ! [B_35,C_36] :
      ( k2_xboole_0(B_35,C_36) = B_35
      | ~ r1_tarski(C_36,B_35) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_178])).

tff(c_208,plain,(
    k2_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_188])).

tff(c_143,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),A_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_212,plain,
    ( k2_xboole_0('#skF_2','#skF_1') = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_143])).

tff(c_237,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_80,c_212])).

tff(c_288,plain,(
    ! [C_38,A_39,B_40] :
      ( k2_xboole_0(k10_relat_1(C_38,A_39),k10_relat_1(C_38,B_40)) = k10_relat_1(C_38,k2_xboole_0(A_39,B_40))
      | ~ v1_relat_1(C_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_739,plain,(
    ! [C_53,A_54,B_55] :
      ( r1_tarski(k10_relat_1(C_53,A_54),k10_relat_1(C_53,k2_xboole_0(A_54,B_55)))
      | ~ v1_relat_1(C_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_8])).

tff(c_877,plain,(
    ! [C_58] :
      ( r1_tarski(k10_relat_1(C_58,'#skF_1'),k10_relat_1(C_58,'#skF_2'))
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_237,c_739])).

tff(c_18,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_888,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_877,c_18])).

tff(c_896,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_888])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:26:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.58/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  %$ r1_tarski > v1_relat_1 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.58/1.39  
% 2.58/1.39  %Foreground sorts:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Background operators:
% 2.58/1.39  
% 2.58/1.39  
% 2.58/1.39  %Foreground operators:
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.58/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.58/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.58/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.58/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.58/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.58/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.58/1.39  
% 2.58/1.40  tff(f_54, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 2.58/1.40  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.58/1.40  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.58/1.40  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.58/1.40  tff(f_39, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 2.58/1.40  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.58/1.40  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.58/1.40  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.40  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.40  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.58/1.40  tff(c_59, plain, (![A_20, B_21]: (k3_tarski(k2_tarski(A_20, B_21))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.40  tff(c_74, plain, (![B_22, A_23]: (k3_tarski(k2_tarski(B_22, A_23))=k2_xboole_0(A_23, B_22))), inference(superposition, [status(thm), theory('equality')], [c_12, c_59])).
% 2.58/1.40  tff(c_14, plain, (![A_10, B_11]: (k3_tarski(k2_tarski(A_10, B_11))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.40  tff(c_80, plain, (![B_22, A_23]: (k2_xboole_0(B_22, A_23)=k2_xboole_0(A_23, B_22))), inference(superposition, [status(thm), theory('equality')], [c_74, c_14])).
% 2.58/1.40  tff(c_20, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.40  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k2_xboole_0(A_5, C_7), B_6) | ~r1_tarski(C_7, B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.58/1.40  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.58/1.40  tff(c_136, plain, (![B_26, A_27]: (B_26=A_27 | ~r1_tarski(B_26, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.58/1.40  tff(c_174, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=A_33 | ~r1_tarski(k2_xboole_0(A_33, B_34), A_33))), inference(resolution, [status(thm)], [c_8, c_136])).
% 2.58/1.40  tff(c_178, plain, (![B_6, C_7]: (k2_xboole_0(B_6, C_7)=B_6 | ~r1_tarski(C_7, B_6) | ~r1_tarski(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_174])).
% 2.58/1.40  tff(c_188, plain, (![B_35, C_36]: (k2_xboole_0(B_35, C_36)=B_35 | ~r1_tarski(C_36, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_178])).
% 2.58/1.40  tff(c_208, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_20, c_188])).
% 2.58/1.40  tff(c_143, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(k2_xboole_0(A_3, B_4), A_3))), inference(resolution, [status(thm)], [c_8, c_136])).
% 2.58/1.40  tff(c_212, plain, (k2_xboole_0('#skF_2', '#skF_1')='#skF_2' | ~r1_tarski('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_208, c_143])).
% 2.58/1.40  tff(c_237, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_80, c_212])).
% 2.58/1.40  tff(c_288, plain, (![C_38, A_39, B_40]: (k2_xboole_0(k10_relat_1(C_38, A_39), k10_relat_1(C_38, B_40))=k10_relat_1(C_38, k2_xboole_0(A_39, B_40)) | ~v1_relat_1(C_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.58/1.40  tff(c_739, plain, (![C_53, A_54, B_55]: (r1_tarski(k10_relat_1(C_53, A_54), k10_relat_1(C_53, k2_xboole_0(A_54, B_55))) | ~v1_relat_1(C_53))), inference(superposition, [status(thm), theory('equality')], [c_288, c_8])).
% 2.58/1.40  tff(c_877, plain, (![C_58]: (r1_tarski(k10_relat_1(C_58, '#skF_1'), k10_relat_1(C_58, '#skF_2')) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_237, c_739])).
% 2.58/1.40  tff(c_18, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.58/1.40  tff(c_888, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_877, c_18])).
% 2.58/1.40  tff(c_896, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_888])).
% 2.58/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.40  
% 2.58/1.40  Inference rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Ref     : 0
% 2.58/1.40  #Sup     : 221
% 2.58/1.40  #Fact    : 0
% 2.58/1.40  #Define  : 0
% 2.58/1.40  #Split   : 1
% 2.58/1.40  #Chain   : 0
% 2.58/1.40  #Close   : 0
% 2.58/1.40  
% 2.58/1.40  Ordering : KBO
% 2.58/1.40  
% 2.58/1.40  Simplification rules
% 2.58/1.40  ----------------------
% 2.58/1.40  #Subsume      : 12
% 2.58/1.40  #Demod        : 161
% 2.58/1.40  #Tautology    : 127
% 2.58/1.40  #SimpNegUnit  : 0
% 2.58/1.40  #BackRed      : 0
% 2.58/1.41  
% 2.58/1.41  #Partial instantiations: 0
% 2.58/1.41  #Strategies tried      : 1
% 2.58/1.41  
% 2.58/1.41  Timing (in seconds)
% 2.58/1.41  ----------------------
% 2.58/1.41  Preprocessing        : 0.27
% 2.58/1.41  Parsing              : 0.15
% 2.58/1.41  CNF conversion       : 0.02
% 2.58/1.41  Main loop            : 0.38
% 2.58/1.41  Inferencing          : 0.13
% 2.58/1.41  Reduction            : 0.14
% 2.58/1.41  Demodulation         : 0.12
% 2.58/1.41  BG Simplification    : 0.02
% 2.58/1.41  Subsumption          : 0.07
% 2.58/1.41  Abstraction          : 0.02
% 2.58/1.41  MUC search           : 0.00
% 2.58/1.41  Cooper               : 0.00
% 2.58/1.41  Total                : 0.67
% 2.58/1.41  Index Insertion      : 0.00
% 2.58/1.41  Index Deletion       : 0.00
% 2.58/1.41  Index Matching       : 0.00
% 2.58/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
