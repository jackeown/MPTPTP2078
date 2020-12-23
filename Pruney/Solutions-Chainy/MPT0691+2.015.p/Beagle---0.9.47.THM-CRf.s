%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:41 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   26 (  43 expanded)
%              Depth                    :   12
%              Number of atoms          :   71 ( 153 expanded)
%              Number of equality atoms :   26 (  45 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_26,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_14,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_191,plain,(
    ! [B_42,A_43] :
      ( k1_relat_1(k7_relat_1(B_42,A_43)) = A_43
      | ~ r1_tarski(A_43,k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_202,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_191])).

tff(c_211,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_202])).

tff(c_16,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_219,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_16])).

tff(c_333,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_336,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_333])).

tff(c_340,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_336])).

tff(c_342,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_363,plain,(
    ! [A_59,C_60,B_61] :
      ( k9_relat_1(k7_relat_1(A_59,C_60),B_61) = k9_relat_1(A_59,B_61)
      | ~ r1_tarski(B_61,C_60)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_341,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_369,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_341])).

tff(c_386,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_6,c_369])).

tff(c_20,plain,(
    ! [A_17] :
      ( k10_relat_1(A_17,k2_relat_1(A_17)) = k1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_394,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_20])).

tff(c_398,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_211,c_394])).

tff(c_262,plain,(
    ! [A_49,C_50,B_51] :
      ( k3_xboole_0(A_49,k10_relat_1(C_50,B_51)) = k10_relat_1(k7_relat_1(C_50,A_49),B_51)
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_68,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_83,plain,(
    ! [B_32,A_33] : k1_setfam_1(k2_tarski(B_32,A_33)) = k3_xboole_0(A_33,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_68])).

tff(c_12,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_35,A_36] : k3_xboole_0(B_35,A_36) = k3_xboole_0(A_36,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_130,plain,(
    ! [B_35,A_36] : r1_tarski(k3_xboole_0(B_35,A_36),A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_8])).

tff(c_475,plain,(
    ! [C_63,A_64,B_65] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_63,A_64),B_65),k10_relat_1(C_63,B_65))
      | ~ v1_relat_1(C_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_262,c_130])).

tff(c_480,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_475])).

tff(c_493,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_480])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:24:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.49  
% 2.70/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.49  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.70/1.49  
% 2.70/1.49  %Foreground sorts:
% 2.70/1.49  
% 2.70/1.49  
% 2.70/1.49  %Background operators:
% 2.70/1.49  
% 2.70/1.49  
% 2.70/1.49  %Foreground operators:
% 2.70/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.70/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.70/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.70/1.49  
% 2.70/1.50  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.70/1.50  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.70/1.50  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.70/1.50  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.70/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.70/1.50  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.70/1.50  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.70/1.50  tff(f_66, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.70/1.50  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.70/1.50  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.70/1.50  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.70/1.50  tff(c_26, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.50  tff(c_30, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.50  tff(c_14, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.50  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.70/1.50  tff(c_191, plain, (![B_42, A_43]: (k1_relat_1(k7_relat_1(B_42, A_43))=A_43 | ~r1_tarski(A_43, k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.50  tff(c_202, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_28, c_191])).
% 2.70/1.50  tff(c_211, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_202])).
% 2.70/1.50  tff(c_16, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.70/1.50  tff(c_219, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_211, c_16])).
% 2.70/1.50  tff(c_333, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_219])).
% 2.70/1.50  tff(c_336, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_333])).
% 2.70/1.50  tff(c_340, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_336])).
% 2.70/1.50  tff(c_342, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_219])).
% 2.70/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.70/1.50  tff(c_363, plain, (![A_59, C_60, B_61]: (k9_relat_1(k7_relat_1(A_59, C_60), B_61)=k9_relat_1(A_59, B_61) | ~r1_tarski(B_61, C_60) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.50  tff(c_341, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_219])).
% 2.70/1.50  tff(c_369, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_363, c_341])).
% 2.70/1.50  tff(c_386, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_6, c_369])).
% 2.70/1.50  tff(c_20, plain, (![A_17]: (k10_relat_1(A_17, k2_relat_1(A_17))=k1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.50  tff(c_394, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_386, c_20])).
% 2.70/1.50  tff(c_398, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_342, c_211, c_394])).
% 2.70/1.50  tff(c_262, plain, (![A_49, C_50, B_51]: (k3_xboole_0(A_49, k10_relat_1(C_50, B_51))=k10_relat_1(k7_relat_1(C_50, A_49), B_51) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.70/1.50  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.70/1.50  tff(c_68, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.50  tff(c_83, plain, (![B_32, A_33]: (k1_setfam_1(k2_tarski(B_32, A_33))=k3_xboole_0(A_33, B_32))), inference(superposition, [status(thm), theory('equality')], [c_10, c_68])).
% 2.70/1.50  tff(c_12, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.50  tff(c_115, plain, (![B_35, A_36]: (k3_xboole_0(B_35, A_36)=k3_xboole_0(A_36, B_35))), inference(superposition, [status(thm), theory('equality')], [c_83, c_12])).
% 2.70/1.50  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.50  tff(c_130, plain, (![B_35, A_36]: (r1_tarski(k3_xboole_0(B_35, A_36), A_36))), inference(superposition, [status(thm), theory('equality')], [c_115, c_8])).
% 2.70/1.50  tff(c_475, plain, (![C_63, A_64, B_65]: (r1_tarski(k10_relat_1(k7_relat_1(C_63, A_64), B_65), k10_relat_1(C_63, B_65)) | ~v1_relat_1(C_63))), inference(superposition, [status(thm), theory('equality')], [c_262, c_130])).
% 2.70/1.50  tff(c_480, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_398, c_475])).
% 2.70/1.50  tff(c_493, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_480])).
% 2.70/1.50  tff(c_495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_493])).
% 2.70/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.50  
% 2.70/1.50  Inference rules
% 2.70/1.50  ----------------------
% 2.70/1.50  #Ref     : 0
% 2.70/1.50  #Sup     : 116
% 2.70/1.50  #Fact    : 0
% 2.70/1.50  #Define  : 0
% 2.70/1.50  #Split   : 2
% 2.70/1.50  #Chain   : 0
% 2.70/1.50  #Close   : 0
% 2.70/1.50  
% 2.70/1.50  Ordering : KBO
% 2.70/1.50  
% 2.70/1.50  Simplification rules
% 2.70/1.50  ----------------------
% 2.70/1.50  #Subsume      : 7
% 2.70/1.50  #Demod        : 42
% 2.70/1.50  #Tautology    : 60
% 2.70/1.50  #SimpNegUnit  : 1
% 2.70/1.50  #BackRed      : 1
% 2.70/1.50  
% 2.70/1.50  #Partial instantiations: 0
% 2.70/1.50  #Strategies tried      : 1
% 2.70/1.50  
% 2.70/1.50  Timing (in seconds)
% 2.70/1.50  ----------------------
% 2.70/1.50  Preprocessing        : 0.34
% 2.70/1.50  Parsing              : 0.17
% 2.70/1.50  CNF conversion       : 0.02
% 2.70/1.50  Main loop            : 0.26
% 2.70/1.50  Inferencing          : 0.09
% 2.70/1.50  Reduction            : 0.09
% 2.70/1.50  Demodulation         : 0.07
% 2.70/1.50  BG Simplification    : 0.02
% 2.70/1.50  Subsumption          : 0.05
% 2.70/1.51  Abstraction          : 0.02
% 2.70/1.51  MUC search           : 0.00
% 2.70/1.51  Cooper               : 0.00
% 2.70/1.51  Total                : 0.63
% 2.70/1.51  Index Insertion      : 0.00
% 2.70/1.51  Index Deletion       : 0.00
% 2.70/1.51  Index Matching       : 0.00
% 2.70/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
