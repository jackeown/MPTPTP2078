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
% DateTime   : Thu Dec  3 10:01:48 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   47 (  66 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   46 (  78 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [B_11,A_10] : k2_tarski(B_11,A_10) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_58,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_104,plain,(
    ! [B_36,A_37] : k1_setfam_1(k2_tarski(B_36,A_37)) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_16,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_110,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_16])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_30,B_31] :
      ( k2_xboole_0(A_30,B_31) = B_31
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_73])).

tff(c_273,plain,(
    ! [C_52,A_53,B_54] :
      ( k2_xboole_0(k10_relat_1(C_52,A_53),k10_relat_1(C_52,B_54)) = k10_relat_1(C_52,k2_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_288,plain,(
    ! [C_55,A_56,B_57] :
      ( r1_tarski(k10_relat_1(C_55,A_56),k10_relat_1(C_55,k2_xboole_0(A_56,B_57)))
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_8])).

tff(c_305,plain,(
    ! [C_58,A_59,B_60] :
      ( r1_tarski(k10_relat_1(C_58,k3_xboole_0(A_59,B_60)),k10_relat_1(C_58,A_59))
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_288])).

tff(c_311,plain,(
    ! [C_58,B_36,A_37] :
      ( r1_tarski(k10_relat_1(C_58,k3_xboole_0(B_36,A_37)),k10_relat_1(C_58,A_37))
      | ~ v1_relat_1(C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_305])).

tff(c_303,plain,(
    ! [C_55,A_3,B_4] :
      ( r1_tarski(k10_relat_1(C_55,k3_xboole_0(A_3,B_4)),k10_relat_1(C_55,A_3))
      | ~ v1_relat_1(C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_288])).

tff(c_229,plain,(
    ! [A_47,B_48,C_49] :
      ( r1_tarski(A_47,k3_xboole_0(B_48,C_49))
      | ~ r1_tarski(A_47,C_49)
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_20,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_242,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_229,c_20])).

tff(c_418,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_242])).

tff(c_421,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_303,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_421])).

tff(c_426,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_242])).

tff(c_430,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_311,c_426])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:18:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.71  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.72  
% 2.61/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.72  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.61/1.72  
% 2.61/1.72  %Foreground sorts:
% 2.61/1.72  
% 2.61/1.72  
% 2.61/1.72  %Background operators:
% 2.61/1.72  
% 2.61/1.72  
% 2.61/1.72  %Foreground operators:
% 2.61/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.72  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.72  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.72  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.72  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.72  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.72  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.61/1.72  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.72  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.72  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.61/1.72  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.72  
% 2.80/1.74  tff(f_56, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 2.80/1.74  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.80/1.74  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.80/1.74  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.80/1.74  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.80/1.74  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.80/1.74  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.80/1.74  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.80/1.74  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.80/1.74  tff(c_10, plain, (![B_11, A_10]: (k2_tarski(B_11, A_10)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.74  tff(c_58, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.74  tff(c_104, plain, (![B_36, A_37]: (k1_setfam_1(k2_tarski(B_36, A_37))=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_10, c_58])).
% 2.80/1.74  tff(c_16, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.74  tff(c_110, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(superposition, [status(thm), theory('equality')], [c_104, c_16])).
% 2.80/1.74  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.74  tff(c_73, plain, (![A_30, B_31]: (k2_xboole_0(A_30, B_31)=B_31 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.74  tff(c_80, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_73])).
% 2.80/1.74  tff(c_273, plain, (![C_52, A_53, B_54]: (k2_xboole_0(k10_relat_1(C_52, A_53), k10_relat_1(C_52, B_54))=k10_relat_1(C_52, k2_xboole_0(A_53, B_54)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.74  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.74  tff(c_288, plain, (![C_55, A_56, B_57]: (r1_tarski(k10_relat_1(C_55, A_56), k10_relat_1(C_55, k2_xboole_0(A_56, B_57))) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_273, c_8])).
% 2.80/1.74  tff(c_305, plain, (![C_58, A_59, B_60]: (r1_tarski(k10_relat_1(C_58, k3_xboole_0(A_59, B_60)), k10_relat_1(C_58, A_59)) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_80, c_288])).
% 2.80/1.74  tff(c_311, plain, (![C_58, B_36, A_37]: (r1_tarski(k10_relat_1(C_58, k3_xboole_0(B_36, A_37)), k10_relat_1(C_58, A_37)) | ~v1_relat_1(C_58))), inference(superposition, [status(thm), theory('equality')], [c_110, c_305])).
% 2.80/1.74  tff(c_303, plain, (![C_55, A_3, B_4]: (r1_tarski(k10_relat_1(C_55, k3_xboole_0(A_3, B_4)), k10_relat_1(C_55, A_3)) | ~v1_relat_1(C_55))), inference(superposition, [status(thm), theory('equality')], [c_80, c_288])).
% 2.80/1.74  tff(c_229, plain, (![A_47, B_48, C_49]: (r1_tarski(A_47, k3_xboole_0(B_48, C_49)) | ~r1_tarski(A_47, C_49) | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.74  tff(c_20, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.80/1.74  tff(c_242, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_229, c_20])).
% 2.80/1.74  tff(c_418, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_242])).
% 2.80/1.74  tff(c_421, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_303, c_418])).
% 2.80/1.74  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_421])).
% 2.80/1.74  tff(c_426, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_242])).
% 2.80/1.74  tff(c_430, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_311, c_426])).
% 2.80/1.74  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_430])).
% 2.80/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.74  
% 2.80/1.74  Inference rules
% 2.80/1.74  ----------------------
% 2.80/1.74  #Ref     : 0
% 2.80/1.74  #Sup     : 101
% 2.80/1.74  #Fact    : 0
% 2.80/1.74  #Define  : 0
% 2.80/1.74  #Split   : 1
% 2.80/1.74  #Chain   : 0
% 2.80/1.74  #Close   : 0
% 2.80/1.74  
% 2.80/1.74  Ordering : KBO
% 2.80/1.74  
% 2.80/1.74  Simplification rules
% 2.80/1.74  ----------------------
% 2.80/1.74  #Subsume      : 18
% 2.80/1.74  #Demod        : 23
% 2.80/1.74  #Tautology    : 60
% 2.80/1.74  #SimpNegUnit  : 0
% 2.80/1.74  #BackRed      : 0
% 2.80/1.74  
% 2.80/1.74  #Partial instantiations: 0
% 2.80/1.74  #Strategies tried      : 1
% 2.80/1.74  
% 2.80/1.74  Timing (in seconds)
% 2.80/1.74  ----------------------
% 2.80/1.74  Preprocessing        : 0.45
% 2.80/1.75  Parsing              : 0.23
% 2.80/1.75  CNF conversion       : 0.03
% 2.80/1.75  Main loop            : 0.38
% 2.80/1.75  Inferencing          : 0.15
% 2.80/1.75  Reduction            : 0.13
% 2.80/1.75  Demodulation         : 0.10
% 2.80/1.75  BG Simplification    : 0.02
% 2.80/1.75  Subsumption          : 0.06
% 2.80/1.75  Abstraction          : 0.02
% 2.80/1.75  MUC search           : 0.00
% 2.80/1.75  Cooper               : 0.00
% 2.80/1.75  Total                : 0.87
% 2.80/1.75  Index Insertion      : 0.00
% 2.80/1.75  Index Deletion       : 0.00
% 2.80/1.75  Index Matching       : 0.00
% 2.80/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
