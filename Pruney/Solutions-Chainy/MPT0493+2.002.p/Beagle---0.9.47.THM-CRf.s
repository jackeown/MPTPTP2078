%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:36 EST 2020

% Result     : Theorem 5.24s
% Output     : CNFRefutation 5.24s
% Verified   : 
% Statistics : Number of formulae       :   53 (  89 expanded)
%              Number of leaves         :   22 (  39 expanded)
%              Depth                    :   11
%              Number of atoms          :   47 (  93 expanded)
%              Number of equality atoms :   35 (  67 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_18,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_26,B_27] :
      ( k2_xboole_0(A_26,B_27) = B_27
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_115,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_103])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_129,plain,(
    ! [A_29,B_30] : k2_xboole_0(k3_xboole_0(A_29,B_30),A_29) = A_29 ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_135,plain,(
    ! [A_29,B_30] : k2_xboole_0(A_29,k3_xboole_0(A_29,B_30)) = A_29 ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_358,plain,(
    ! [A_45,B_46,C_47] : k2_xboole_0(k3_xboole_0(A_45,B_46),k3_xboole_0(A_45,C_47)) = k3_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_413,plain,(
    ! [A_3,C_47] : k3_xboole_0(A_3,k2_xboole_0(A_3,C_47)) = k2_xboole_0(A_3,k3_xboole_0(A_3,C_47)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_358])).

tff(c_425,plain,(
    ! [A_48,C_49] : k3_xboole_0(A_48,k2_xboole_0(A_48,C_49)) = A_48 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_413])).

tff(c_478,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_425])).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_171,plain,(
    ! [A_33,B_34] : k1_setfam_1(k2_tarski(A_33,B_34)) = k3_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_187,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(B_36,A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_171])).

tff(c_14,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [B_36,A_35] : k3_xboole_0(B_36,A_35) = k3_xboole_0(A_35,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_210,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_14])).

tff(c_228,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,k3_xboole_0(A_38,B_37)) = B_37 ),
    inference(superposition,[status(thm),theory(equality)],[c_210,c_135])).

tff(c_416,plain,(
    ! [A_3,B_46] : k3_xboole_0(A_3,k2_xboole_0(B_46,A_3)) = k2_xboole_0(k3_xboole_0(A_3,B_46),A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_358])).

tff(c_629,plain,(
    ! [A_54,B_55] : k3_xboole_0(A_54,k2_xboole_0(B_55,A_54)) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_2,c_416])).

tff(c_4562,plain,(
    ! [A_137,B_138] : k3_xboole_0(k3_xboole_0(A_137,B_138),B_138) = k3_xboole_0(A_137,B_138) ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_629])).

tff(c_8167,plain,(
    ! [B_171,A_172] : k3_xboole_0(k3_xboole_0(B_171,A_172),B_171) = k3_xboole_0(A_172,B_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_193,c_4562])).

tff(c_8379,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_478,c_8167])).

tff(c_8448,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8379])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k3_xboole_0(k1_relat_1(B_17),A_16) = k1_relat_1(k7_relat_1(B_17,A_16))
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_8539,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8448,c_16])).

tff(c_8595,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_8539])).

tff(c_8597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_8595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:56:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.24/2.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.15  
% 5.24/2.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.15  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.24/2.15  
% 5.24/2.15  %Foreground sorts:
% 5.24/2.15  
% 5.24/2.15  
% 5.24/2.15  %Background operators:
% 5.24/2.15  
% 5.24/2.15  
% 5.24/2.15  %Foreground operators:
% 5.24/2.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.24/2.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.24/2.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.24/2.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.24/2.15  tff('#skF_2', type, '#skF_2': $i).
% 5.24/2.15  tff('#skF_1', type, '#skF_1': $i).
% 5.24/2.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.24/2.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.24/2.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.24/2.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.24/2.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.24/2.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.24/2.15  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.24/2.15  
% 5.24/2.16  tff(f_52, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 5.24/2.16  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.24/2.16  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 5.24/2.16  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.24/2.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.24/2.16  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_xboole_1)).
% 5.24/2.16  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.24/2.16  tff(f_41, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.24/2.16  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.24/2.16  tff(c_18, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.24/2.16  tff(c_22, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.24/2.16  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.24/2.16  tff(c_20, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.24/2.16  tff(c_103, plain, (![A_26, B_27]: (k2_xboole_0(A_26, B_27)=B_27 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.24/2.16  tff(c_115, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_103])).
% 5.24/2.16  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.24/2.16  tff(c_129, plain, (![A_29, B_30]: (k2_xboole_0(k3_xboole_0(A_29, B_30), A_29)=A_29)), inference(resolution, [status(thm)], [c_8, c_103])).
% 5.24/2.16  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.24/2.16  tff(c_135, plain, (![A_29, B_30]: (k2_xboole_0(A_29, k3_xboole_0(A_29, B_30))=A_29)), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 5.24/2.16  tff(c_358, plain, (![A_45, B_46, C_47]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k3_xboole_0(A_45, C_47))=k3_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.24/2.16  tff(c_413, plain, (![A_3, C_47]: (k3_xboole_0(A_3, k2_xboole_0(A_3, C_47))=k2_xboole_0(A_3, k3_xboole_0(A_3, C_47)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_358])).
% 5.24/2.16  tff(c_425, plain, (![A_48, C_49]: (k3_xboole_0(A_48, k2_xboole_0(A_48, C_49))=A_48)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_413])).
% 5.24/2.16  tff(c_478, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_115, c_425])).
% 5.24/2.16  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.24/2.16  tff(c_171, plain, (![A_33, B_34]: (k1_setfam_1(k2_tarski(A_33, B_34))=k3_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.24/2.16  tff(c_187, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(B_36, A_35))), inference(superposition, [status(thm), theory('equality')], [c_12, c_171])).
% 5.24/2.16  tff(c_14, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.24/2.16  tff(c_193, plain, (![B_36, A_35]: (k3_xboole_0(B_36, A_35)=k3_xboole_0(A_35, B_36))), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 5.24/2.16  tff(c_210, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_187, c_14])).
% 5.24/2.16  tff(c_228, plain, (![B_37, A_38]: (k2_xboole_0(B_37, k3_xboole_0(A_38, B_37))=B_37)), inference(superposition, [status(thm), theory('equality')], [c_210, c_135])).
% 5.24/2.16  tff(c_416, plain, (![A_3, B_46]: (k3_xboole_0(A_3, k2_xboole_0(B_46, A_3))=k2_xboole_0(k3_xboole_0(A_3, B_46), A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_358])).
% 5.24/2.16  tff(c_629, plain, (![A_54, B_55]: (k3_xboole_0(A_54, k2_xboole_0(B_55, A_54))=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_135, c_2, c_416])).
% 5.24/2.16  tff(c_4562, plain, (![A_137, B_138]: (k3_xboole_0(k3_xboole_0(A_137, B_138), B_138)=k3_xboole_0(A_137, B_138))), inference(superposition, [status(thm), theory('equality')], [c_228, c_629])).
% 5.24/2.16  tff(c_8167, plain, (![B_171, A_172]: (k3_xboole_0(k3_xboole_0(B_171, A_172), B_171)=k3_xboole_0(A_172, B_171))), inference(superposition, [status(thm), theory('equality')], [c_193, c_4562])).
% 5.24/2.16  tff(c_8379, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_478, c_8167])).
% 5.24/2.16  tff(c_8448, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8379])).
% 5.24/2.16  tff(c_16, plain, (![B_17, A_16]: (k3_xboole_0(k1_relat_1(B_17), A_16)=k1_relat_1(k7_relat_1(B_17, A_16)) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.24/2.16  tff(c_8539, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8448, c_16])).
% 5.24/2.16  tff(c_8595, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_8539])).
% 5.24/2.16  tff(c_8597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_8595])).
% 5.24/2.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.24/2.16  
% 5.24/2.16  Inference rules
% 5.24/2.16  ----------------------
% 5.24/2.16  #Ref     : 0
% 5.24/2.16  #Sup     : 2136
% 5.24/2.16  #Fact    : 0
% 5.24/2.16  #Define  : 0
% 5.24/2.16  #Split   : 0
% 5.24/2.16  #Chain   : 0
% 5.24/2.16  #Close   : 0
% 5.24/2.16  
% 5.24/2.16  Ordering : KBO
% 5.24/2.16  
% 5.24/2.16  Simplification rules
% 5.24/2.16  ----------------------
% 5.24/2.16  #Subsume      : 46
% 5.24/2.16  #Demod        : 1824
% 5.24/2.16  #Tautology    : 1439
% 5.24/2.16  #SimpNegUnit  : 1
% 5.24/2.16  #BackRed      : 0
% 5.24/2.16  
% 5.24/2.16  #Partial instantiations: 0
% 5.24/2.16  #Strategies tried      : 1
% 5.24/2.16  
% 5.24/2.16  Timing (in seconds)
% 5.24/2.16  ----------------------
% 5.39/2.17  Preprocessing        : 0.28
% 5.39/2.17  Parsing              : 0.15
% 5.39/2.17  CNF conversion       : 0.02
% 5.39/2.17  Main loop            : 1.11
% 5.39/2.17  Inferencing          : 0.32
% 5.39/2.17  Reduction            : 0.55
% 5.39/2.17  Demodulation         : 0.47
% 5.39/2.17  BG Simplification    : 0.04
% 5.39/2.17  Subsumption          : 0.15
% 5.39/2.17  Abstraction          : 0.06
% 5.39/2.17  MUC search           : 0.00
% 5.39/2.17  Cooper               : 0.00
% 5.39/2.17  Total                : 1.42
% 5.39/2.17  Index Insertion      : 0.00
% 5.39/2.17  Index Deletion       : 0.00
% 5.39/2.17  Index Matching       : 0.00
% 5.39/2.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
