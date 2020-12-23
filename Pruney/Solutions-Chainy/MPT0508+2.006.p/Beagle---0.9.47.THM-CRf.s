%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:55 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
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
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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
             => r1_tarski(k7_relat_1(C,A),k7_relat_1(D,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

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

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => ( r1_tarski(B,C)
           => r1_tarski(k7_relat_1(B,A),k7_relat_1(C,A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_relat_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k7_relat_1(B_18,A_17),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

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
    ! [A_17] :
      ( r1_tarski(k7_relat_1('#skF_3',A_17),'#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_14,c_150])).

tff(c_159,plain,(
    ! [A_34] : r1_tarski(k7_relat_1('#skF_3',A_34),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_182,plain,(
    ! [A_37] : k3_xboole_0(k7_relat_1('#skF_3',A_37),'#skF_4') = k7_relat_1('#skF_3',A_37) ),
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
      ( v1_relat_1(k7_relat_1('#skF_3',A_37))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_41])).

tff(c_209,plain,(
    ! [A_37] : v1_relat_1(k7_relat_1('#skF_3',A_37)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_188])).

tff(c_157,plain,(
    ! [A_17] : r1_tarski(k7_relat_1('#skF_3',A_17),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_154])).

tff(c_10,plain,(
    ! [C_12,A_10,B_11] :
      ( k7_relat_1(k7_relat_1(C_12,A_10),B_11) = k7_relat_1(C_12,A_10)
      | ~ r1_tarski(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_293,plain,(
    ! [B_49,A_50,C_51] :
      ( r1_tarski(k7_relat_1(B_49,A_50),k7_relat_1(C_51,A_50))
      | ~ r1_tarski(B_49,C_51)
      | ~ v1_relat_1(C_51)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1642,plain,(
    ! [C_114,A_115,C_116,B_117] :
      ( r1_tarski(k7_relat_1(C_114,A_115),k7_relat_1(C_116,B_117))
      | ~ r1_tarski(k7_relat_1(C_114,A_115),C_116)
      | ~ v1_relat_1(C_116)
      | ~ v1_relat_1(k7_relat_1(C_114,A_115))
      | ~ r1_tarski(A_115,B_117)
      | ~ v1_relat_1(C_114) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_293])).

tff(c_16,plain,(
    ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),k7_relat_1('#skF_4','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1690,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_3','#skF_1'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1642,c_16])).

tff(c_1735,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_18,c_209,c_22,c_157,c_1690])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:31:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.86  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.86  
% 4.12/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.86  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.86  
% 4.12/1.86  %Foreground sorts:
% 4.12/1.86  
% 4.12/1.86  
% 4.12/1.86  %Background operators:
% 4.12/1.86  
% 4.12/1.86  
% 4.12/1.86  %Foreground operators:
% 4.12/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.86  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.12/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.12/1.86  
% 4.12/1.88  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (![D]: (v1_relat_1(D) => ((r1_tarski(C, D) & r1_tarski(A, B)) => r1_tarski(k7_relat_1(C, A), k7_relat_1(D, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_relat_1)).
% 4.12/1.88  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 4.12/1.88  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.12/1.88  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.12/1.88  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.12/1.88  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 4.12/1.88  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 4.12/1.88  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (r1_tarski(B, C) => r1_tarski(k7_relat_1(B, A), k7_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t105_relat_1)).
% 4.12/1.88  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.88  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.88  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.88  tff(c_14, plain, (![B_18, A_17]: (r1_tarski(k7_relat_1(B_18, A_17), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.12/1.88  tff(c_20, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.88  tff(c_138, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(B_32, C_31) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.12/1.88  tff(c_150, plain, (![A_33]: (r1_tarski(A_33, '#skF_4') | ~r1_tarski(A_33, '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_138])).
% 4.12/1.88  tff(c_154, plain, (![A_17]: (r1_tarski(k7_relat_1('#skF_3', A_17), '#skF_4') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_14, c_150])).
% 4.12/1.88  tff(c_159, plain, (![A_34]: (r1_tarski(k7_relat_1('#skF_3', A_34), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 4.12/1.88  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.12/1.88  tff(c_182, plain, (![A_37]: (k3_xboole_0(k7_relat_1('#skF_3', A_37), '#skF_4')=k7_relat_1('#skF_3', A_37))), inference(resolution, [status(thm)], [c_159, c_6])).
% 4.12/1.88  tff(c_26, plain, (![B_22, A_23]: (k3_xboole_0(B_22, A_23)=k3_xboole_0(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.12/1.88  tff(c_8, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.12/1.88  tff(c_41, plain, (![B_22, A_23]: (v1_relat_1(k3_xboole_0(B_22, A_23)) | ~v1_relat_1(A_23))), inference(superposition, [status(thm), theory('equality')], [c_26, c_8])).
% 4.12/1.88  tff(c_188, plain, (![A_37]: (v1_relat_1(k7_relat_1('#skF_3', A_37)) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_182, c_41])).
% 4.12/1.88  tff(c_209, plain, (![A_37]: (v1_relat_1(k7_relat_1('#skF_3', A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_188])).
% 4.12/1.88  tff(c_157, plain, (![A_17]: (r1_tarski(k7_relat_1('#skF_3', A_17), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_154])).
% 4.12/1.88  tff(c_10, plain, (![C_12, A_10, B_11]: (k7_relat_1(k7_relat_1(C_12, A_10), B_11)=k7_relat_1(C_12, A_10) | ~r1_tarski(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.12/1.88  tff(c_293, plain, (![B_49, A_50, C_51]: (r1_tarski(k7_relat_1(B_49, A_50), k7_relat_1(C_51, A_50)) | ~r1_tarski(B_49, C_51) | ~v1_relat_1(C_51) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.12/1.88  tff(c_1642, plain, (![C_114, A_115, C_116, B_117]: (r1_tarski(k7_relat_1(C_114, A_115), k7_relat_1(C_116, B_117)) | ~r1_tarski(k7_relat_1(C_114, A_115), C_116) | ~v1_relat_1(C_116) | ~v1_relat_1(k7_relat_1(C_114, A_115)) | ~r1_tarski(A_115, B_117) | ~v1_relat_1(C_114))), inference(superposition, [status(thm), theory('equality')], [c_10, c_293])).
% 4.12/1.88  tff(c_16, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), k7_relat_1('#skF_4', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.12/1.88  tff(c_1690, plain, (~r1_tarski(k7_relat_1('#skF_3', '#skF_1'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski('#skF_1', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_1642, c_16])).
% 4.12/1.88  tff(c_1735, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_18, c_209, c_22, c_157, c_1690])).
% 4.12/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.88  
% 4.12/1.88  Inference rules
% 4.12/1.88  ----------------------
% 4.12/1.88  #Ref     : 0
% 4.12/1.88  #Sup     : 399
% 4.12/1.88  #Fact    : 0
% 4.12/1.88  #Define  : 0
% 4.12/1.88  #Split   : 5
% 4.12/1.88  #Chain   : 0
% 4.12/1.88  #Close   : 0
% 4.12/1.88  
% 4.12/1.88  Ordering : KBO
% 4.12/1.88  
% 4.12/1.88  Simplification rules
% 4.12/1.88  ----------------------
% 4.12/1.88  #Subsume      : 49
% 4.12/1.88  #Demod        : 222
% 4.12/1.88  #Tautology    : 144
% 4.12/1.88  #SimpNegUnit  : 0
% 4.12/1.88  #BackRed      : 0
% 4.12/1.88  
% 4.12/1.88  #Partial instantiations: 0
% 4.12/1.88  #Strategies tried      : 1
% 4.12/1.88  
% 4.12/1.88  Timing (in seconds)
% 4.12/1.88  ----------------------
% 4.12/1.88  Preprocessing        : 0.29
% 4.12/1.88  Parsing              : 0.16
% 4.12/1.88  CNF conversion       : 0.02
% 4.12/1.88  Main loop            : 0.81
% 4.12/1.88  Inferencing          : 0.27
% 4.12/1.88  Reduction            : 0.26
% 4.12/1.88  Demodulation         : 0.18
% 4.12/1.88  BG Simplification    : 0.03
% 4.12/1.88  Subsumption          : 0.18
% 4.12/1.88  Abstraction          : 0.05
% 4.12/1.88  MUC search           : 0.00
% 4.12/1.88  Cooper               : 0.00
% 4.12/1.88  Total                : 1.12
% 4.12/1.88  Index Insertion      : 0.00
% 4.12/1.88  Index Deletion       : 0.00
% 4.12/1.88  Index Matching       : 0.00
% 4.12/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
