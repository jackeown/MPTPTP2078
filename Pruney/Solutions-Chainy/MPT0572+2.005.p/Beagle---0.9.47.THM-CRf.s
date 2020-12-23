%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:49 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   24 (  33 expanded)
%              Depth                    :    5
%              Number of atoms          :   45 (  79 expanded)
%              Number of equality atoms :   11 (  16 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_82,plain,(
    ! [B_32,A_33] : k1_setfam_1(k2_tarski(B_32,A_33)) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_16,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_105,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [B_34,A_35] : r1_tarski(k3_xboole_0(B_34,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_187,plain,(
    ! [C_46,A_47,B_48] :
      ( k2_xboole_0(k10_relat_1(C_46,A_47),k10_relat_1(C_46,B_48)) = k10_relat_1(C_46,k2_xboole_0(A_47,B_48))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_199,plain,(
    ! [C_49,A_50,B_51] :
      ( r1_tarski(k10_relat_1(C_49,A_50),k10_relat_1(C_49,k2_xboole_0(A_50,B_51)))
      | ~ v1_relat_1(C_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_8])).

tff(c_205,plain,(
    ! [C_49,A_6,B_7] :
      ( r1_tarski(k10_relat_1(C_49,A_6),k10_relat_1(C_49,B_7))
      | ~ v1_relat_1(C_49)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_199])).

tff(c_176,plain,(
    ! [A_43,B_44,C_45] :
      ( r1_tarski(A_43,k3_xboole_0(B_44,C_45))
      | ~ r1_tarski(A_43,C_45)
      | ~ r1_tarski(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_186,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_176,c_20])).

tff(c_207,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_210,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_205,c_207])).

tff(c_214,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22,c_210])).

tff(c_215,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_219,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_205,c_215])).

tff(c_223,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_22,c_219])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:20:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  
% 2.07/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.25  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.25  
% 2.07/1.25  %Foreground sorts:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Background operators:
% 2.07/1.25  
% 2.07/1.25  
% 2.07/1.25  %Foreground operators:
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.25  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.25  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.25  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.25  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.25  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.25  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.25  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.25  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.25  
% 2.07/1.26  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.07/1.26  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.07/1.26  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.07/1.26  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t176_relat_1)).
% 2.07/1.26  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.07/1.26  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 2.07/1.26  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.07/1.26  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.07/1.26  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.26  tff(c_58, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.26  tff(c_82, plain, (![B_32, A_33]: (k1_setfam_1(k2_tarski(B_32, A_33))=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.07/1.26  tff(c_16, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.07/1.26  tff(c_105, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_82, c_16])).
% 2.07/1.26  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.07/1.26  tff(c_120, plain, (![B_34, A_35]: (r1_tarski(k3_xboole_0(B_34, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 2.07/1.26  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.26  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.07/1.26  tff(c_187, plain, (![C_46, A_47, B_48]: (k2_xboole_0(k10_relat_1(C_46, A_47), k10_relat_1(C_46, B_48))=k10_relat_1(C_46, k2_xboole_0(A_47, B_48)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.26  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.26  tff(c_199, plain, (![C_49, A_50, B_51]: (r1_tarski(k10_relat_1(C_49, A_50), k10_relat_1(C_49, k2_xboole_0(A_50, B_51))) | ~v1_relat_1(C_49))), inference(superposition, [status(thm), theory('equality')], [c_187, c_8])).
% 2.07/1.26  tff(c_205, plain, (![C_49, A_6, B_7]: (r1_tarski(k10_relat_1(C_49, A_6), k10_relat_1(C_49, B_7)) | ~v1_relat_1(C_49) | ~r1_tarski(A_6, B_7))), inference(superposition, [status(thm), theory('equality')], [c_6, c_199])).
% 2.07/1.26  tff(c_176, plain, (![A_43, B_44, C_45]: (r1_tarski(A_43, k3_xboole_0(B_44, C_45)) | ~r1_tarski(A_43, C_45) | ~r1_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.26  tff(c_20, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.07/1.26  tff(c_186, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_176, c_20])).
% 2.07/1.26  tff(c_207, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_186])).
% 2.07/1.26  tff(c_210, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_205, c_207])).
% 2.07/1.26  tff(c_214, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_22, c_210])).
% 2.07/1.26  tff(c_215, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_186])).
% 2.07/1.26  tff(c_219, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_205, c_215])).
% 2.07/1.26  tff(c_223, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_22, c_219])).
% 2.07/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  Inference rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Ref     : 0
% 2.07/1.26  #Sup     : 47
% 2.07/1.26  #Fact    : 0
% 2.07/1.26  #Define  : 0
% 2.07/1.26  #Split   : 1
% 2.07/1.26  #Chain   : 0
% 2.07/1.26  #Close   : 0
% 2.07/1.26  
% 2.07/1.26  Ordering : KBO
% 2.07/1.26  
% 2.07/1.26  Simplification rules
% 2.07/1.26  ----------------------
% 2.07/1.26  #Subsume      : 3
% 2.07/1.26  #Demod        : 10
% 2.07/1.26  #Tautology    : 35
% 2.07/1.26  #SimpNegUnit  : 0
% 2.07/1.26  #BackRed      : 0
% 2.07/1.26  
% 2.07/1.26  #Partial instantiations: 0
% 2.07/1.26  #Strategies tried      : 1
% 2.07/1.26  
% 2.07/1.26  Timing (in seconds)
% 2.07/1.26  ----------------------
% 2.07/1.27  Preprocessing        : 0.30
% 2.07/1.27  Parsing              : 0.16
% 2.07/1.27  CNF conversion       : 0.02
% 2.07/1.27  Main loop            : 0.16
% 2.07/1.27  Inferencing          : 0.06
% 2.07/1.27  Reduction            : 0.06
% 2.07/1.27  Demodulation         : 0.05
% 2.07/1.27  BG Simplification    : 0.01
% 2.07/1.27  Subsumption          : 0.03
% 2.07/1.27  Abstraction          : 0.01
% 2.07/1.27  MUC search           : 0.00
% 2.07/1.27  Cooper               : 0.00
% 2.07/1.27  Total                : 0.49
% 2.07/1.27  Index Insertion      : 0.00
% 2.07/1.27  Index Deletion       : 0.00
% 2.07/1.27  Index Matching       : 0.00
% 2.07/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
