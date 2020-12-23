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
% DateTime   : Thu Dec  3 10:00:17 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.89s
% Verified   : 
% Statistics : Number of formulae       :   42 (  60 expanded)
%              Number of leaves         :   19 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 126 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ! [D] :
            ( v1_relat_1(D)
           => ( ( r1_tarski(C,D)
                & r1_tarski(A,B) )
             => r1_tarski(k8_relat_1(A,C),k8_relat_1(B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t133_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k8_relat_1(B,k8_relat_1(A,C)) = k8_relat_1(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t129_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k8_relat_1(A,B),k8_relat_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t132_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(k8_relat_1(A_10,B_11),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_20,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_138,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(B_32,C_31)
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [A_33] :
      ( r1_tarski(A_33,'#skF_4')
      | ~ r1_tarski(A_33,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_138])).

tff(c_154,plain,(
    ! [A_10] :
      ( r1_tarski(k8_relat_1(A_10,'#skF_3'),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_10,c_150])).

tff(c_159,plain,(
    ! [A_34] : r1_tarski(k8_relat_1(A_34,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_37] : k3_xboole_0(k8_relat_1(A_37,'#skF_3'),'#skF_4') = k8_relat_1(A_37,'#skF_3') ),
    inference(resolution,[status(thm)],[c_159,c_6])).

tff(c_26,plain,(
    ! [B_22,A_23] : k3_xboole_0(B_22,A_23) = k3_xboole_0(A_23,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_41,plain,(
    ! [B_22,A_23] :
      ( v1_relat_1(k3_xboole_0(B_22,A_23))
      | ~ v1_relat_1(A_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_188,plain,(
    ! [A_37] :
      ( v1_relat_1(k8_relat_1(A_37,'#skF_3'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_41])).

tff(c_209,plain,(
    ! [A_37] : v1_relat_1(k8_relat_1(A_37,'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_188])).

tff(c_157,plain,(
    ! [A_10] : r1_tarski(k8_relat_1(A_10,'#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).

tff(c_12,plain,(
    ! [B_13,A_12,C_14] :
      ( k8_relat_1(B_13,k8_relat_1(A_12,C_14)) = k8_relat_1(A_12,C_14)
      | ~ r1_tarski(A_12,B_13)
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_293,plain,(
    ! [A_49,B_50,C_51] :
      ( r1_tarski(k8_relat_1(A_49,B_50),k8_relat_1(A_49,C_51))
      | ~ r1_tarski(B_50,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1642,plain,(
    ! [A_114,C_115,B_116,C_117] :
      ( r1_tarski(k8_relat_1(A_114,C_115),k8_relat_1(B_116,C_117))
      | ~ r1_tarski(k8_relat_1(A_114,C_115),C_117)
      | ~ v1_relat_1(C_117)
      | ~ v1_relat_1(k8_relat_1(A_114,C_115))
      | ~ r1_tarski(A_114,B_116)
      | ~ v1_relat_1(C_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_293])).

tff(c_16,plain,(
    ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),k8_relat_1('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1690,plain,
    ( ~ r1_tarski(k8_relat_1('#skF_1','#skF_3'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k8_relat_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1642,c_16])).

tff(c_1735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_209,c_22,c_157,c_1690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n008.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:04:45 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.47/1.63  
% 3.47/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.64  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.89/1.64  
% 3.89/1.64  %Foreground sorts:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Background operators:
% 3.89/1.64  
% 3.89/1.64  
% 3.89/1.64  %Foreground operators:
% 3.89/1.64  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.89/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.89/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.89/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.64  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.89/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.89/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.89/1.64  
% 3.89/1.65  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k8_relat_1(A, C), k8_relat_1(B, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t133_relat_1)).
% 3.89/1.65  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t117_relat_1)).
% 3.89/1.65  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.89/1.65  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.89/1.65  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.89/1.65  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 3.89/1.65  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k8_relat_1(B, k8_relat_1(A, C)) = k8_relat_1(A, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t129_relat_1)).
% 3.89/1.65  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k8_relat_1(A, B), k8_relat_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t132_relat_1)).
% 3.89/1.65  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.89/1.65  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.89/1.65  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.89/1.65  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(k8_relat_1(A_10, B_11), B_11) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.89/1.65  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.89/1.65  tff(c_138, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.89/1.65  tff(c_150, plain, (![A_33]: (r1_tarski(A_33, '#skF_4') | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_138])).
% 3.89/1.65  tff(c_154, plain, (![A_10]: (r1_tarski(k8_relat_1(A_10, '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_10, c_150])).
% 3.89/1.65  tff(c_159, plain, (![A_34]: (r1_tarski(k8_relat_1(A_34, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 3.89/1.65  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.89/1.65  tff(c_182, plain, (![A_37]: (k3_xboole_0(k8_relat_1(A_37, '#skF_3'), '#skF_4')=k8_relat_1(A_37, '#skF_3'))), inference(resolution, [status(thm)], [c_159, c_6])).
% 3.89/1.65  tff(c_26, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.89/1.65  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.89/1.65  tff(c_41, plain, (![B_22, A_23]: (v1_relat_1(k3_xboole_0(B_22, A_23)) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8])).
% 3.89/1.65  tff(c_188, plain, (![A_37]: (v1_relat_1(k8_relat_1(A_37, '#skF_3')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_41])).
% 3.89/1.65  tff(c_209, plain, (![A_37]: (v1_relat_1(k8_relat_1(A_37, '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_188])).
% 3.89/1.65  tff(c_157, plain, (![A_10]: (r1_tarski(k8_relat_1(A_10, '#skF_3'), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 3.89/1.65  tff(c_12, plain, (![B_13, A_12, C_14]: (k8_relat_1(B_13, k8_relat_1(A_12, C_14))=k8_relat_1(A_12, C_14) | ~r1_tarski(A_12, B_13) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.89/1.65  tff(c_293, plain, (![A_49, B_50, C_51]: (r1_tarski(k8_relat_1(A_49, B_50), k8_relat_1(A_49, C_51)) | ~r1_tarski(B_50, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.89/1.65  tff(c_1642, plain, (![A_114, C_115, B_116, C_117]: (r1_tarski(k8_relat_1(A_114, C_115), k8_relat_1(B_116, C_117)) | ~r1_tarski(k8_relat_1(A_114, C_115), C_117) | ~v1_relat_1(C_117) | ~v1_relat_1(k8_relat_1(A_114, C_115)) | ~r1_tarski(A_114, B_116) | ~v1_relat_1(C_115))), inference(superposition, [status(thm), theory('equality')], [c_12, c_293])).
% 3.89/1.65  tff(c_16, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), k8_relat_1('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.89/1.65  tff(c_1690, plain, (~r1_tarski(k8_relat_1('#skF_1', '#skF_3'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k8_relat_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1642, c_16])).
% 3.89/1.65  tff(c_1735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_209, c_22, c_157, c_1690])).
% 3.89/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.65  
% 3.89/1.65  Inference rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Ref     : 0
% 3.89/1.65  #Sup     : 399
% 3.89/1.65  #Fact    : 0
% 3.89/1.65  #Define  : 0
% 3.89/1.65  #Split   : 5
% 3.89/1.65  #Chain   : 0
% 3.89/1.65  #Close   : 0
% 3.89/1.65  
% 3.89/1.65  Ordering : KBO
% 3.89/1.65  
% 3.89/1.65  Simplification rules
% 3.89/1.65  ----------------------
% 3.89/1.65  #Subsume      : 49
% 3.89/1.65  #Demod        : 222
% 3.89/1.65  #Tautology    : 144
% 3.89/1.65  #SimpNegUnit  : 0
% 3.89/1.65  #BackRed      : 0
% 3.89/1.65  
% 3.89/1.65  #Partial instantiations: 0
% 3.89/1.65  #Strategies tried      : 1
% 3.89/1.65  
% 3.89/1.65  Timing (in seconds)
% 3.89/1.65  ----------------------
% 3.89/1.65  Preprocessing        : 0.29
% 3.89/1.65  Parsing              : 0.16
% 3.89/1.65  CNF conversion       : 0.02
% 3.89/1.65  Main loop            : 0.62
% 3.89/1.65  Inferencing          : 0.21
% 3.89/1.65  Reduction            : 0.19
% 3.89/1.65  Demodulation         : 0.14
% 3.89/1.65  BG Simplification    : 0.02
% 3.89/1.65  Subsumption          : 0.14
% 3.89/1.65  Abstraction          : 0.03
% 3.89/1.65  MUC search           : 0.00
% 3.89/1.65  Cooper               : 0.00
% 3.89/1.65  Total                : 0.94
% 3.89/1.65  Index Insertion      : 0.00
% 3.89/1.65  Index Deletion       : 0.00
% 3.89/1.65  Index Matching       : 0.00
% 3.89/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
