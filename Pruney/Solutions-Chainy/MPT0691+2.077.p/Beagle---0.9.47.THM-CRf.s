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
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   53 (  81 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   65 ( 129 expanded)
%              Number of equality atoms :   24 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_61,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_92,plain,(
    ! [B_32,A_33] :
      ( k1_relat_1(k7_relat_1(B_32,A_33)) = A_33
      | ~ r1_tarski(A_33,k1_relat_1(B_32))
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_92])).

tff(c_103,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_99])).

tff(c_18,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_168,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_171,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_168])).

tff(c_175,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_171])).

tff(c_177,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_8,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [B_30,A_31] :
      ( k2_relat_1(k7_relat_1(B_30,A_31)) = k9_relat_1(B_30,A_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_12] :
      ( k10_relat_1(A_12,k2_relat_1(A_12)) = k1_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_234,plain,(
    ! [B_48,A_49] :
      ( k10_relat_1(k7_relat_1(B_48,A_49),k9_relat_1(B_48,A_49)) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_16])).

tff(c_111,plain,(
    ! [A_34,C_35,B_36] :
      ( k3_xboole_0(A_34,k10_relat_1(C_35,B_36)) = k10_relat_1(k7_relat_1(C_35,A_34),B_36)
      | ~ v1_relat_1(C_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_34,C_35,B_36] :
      ( k5_xboole_0(A_34,k10_relat_1(k7_relat_1(C_35,A_34),B_36)) = k4_xboole_0(A_34,k10_relat_1(C_35,B_36))
      | ~ v1_relat_1(C_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_6])).

tff(c_261,plain,(
    ! [A_52,B_53] :
      ( k5_xboole_0(A_52,k1_relat_1(k7_relat_1(B_53,A_52))) = k4_xboole_0(A_52,k10_relat_1(B_53,k9_relat_1(B_53,A_52)))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(k7_relat_1(B_53,A_52))
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_117])).

tff(c_276,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_261])).

tff(c_282,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_177,c_26,c_8,c_276])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  
% 1.95/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.27  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.27  
% 1.95/1.27  %Foreground sorts:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Background operators:
% 1.95/1.27  
% 1.95/1.27  
% 1.95/1.27  %Foreground operators:
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.95/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.27  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.27  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.27  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.95/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.27  
% 1.95/1.28  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.95/1.28  tff(f_64, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 1.95/1.28  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 1.95/1.28  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 1.95/1.28  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.95/1.28  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.95/1.28  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 1.95/1.28  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 1.95/1.28  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.95/1.28  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.28  tff(c_22, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.28  tff(c_61, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.95/1.28  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.28  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.95/1.28  tff(c_24, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.95/1.28  tff(c_92, plain, (![B_32, A_33]: (k1_relat_1(k7_relat_1(B_32, A_33))=A_33 | ~r1_tarski(A_33, k1_relat_1(B_32)) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.28  tff(c_99, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_92])).
% 1.95/1.28  tff(c_103, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_99])).
% 1.95/1.28  tff(c_18, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.95/1.28  tff(c_107, plain, (![A_13]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_103, c_18])).
% 1.95/1.28  tff(c_168, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_107])).
% 1.95/1.28  tff(c_171, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_168])).
% 1.95/1.28  tff(c_175, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_171])).
% 1.95/1.28  tff(c_177, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_107])).
% 1.95/1.28  tff(c_8, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.28  tff(c_80, plain, (![B_30, A_31]: (k2_relat_1(k7_relat_1(B_30, A_31))=k9_relat_1(B_30, A_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.95/1.28  tff(c_16, plain, (![A_12]: (k10_relat_1(A_12, k2_relat_1(A_12))=k1_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.95/1.28  tff(c_234, plain, (![B_48, A_49]: (k10_relat_1(k7_relat_1(B_48, A_49), k9_relat_1(B_48, A_49))=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(superposition, [status(thm), theory('equality')], [c_80, c_16])).
% 1.95/1.28  tff(c_111, plain, (![A_34, C_35, B_36]: (k3_xboole_0(A_34, k10_relat_1(C_35, B_36))=k10_relat_1(k7_relat_1(C_35, A_34), B_36) | ~v1_relat_1(C_35))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.95/1.28  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.28  tff(c_117, plain, (![A_34, C_35, B_36]: (k5_xboole_0(A_34, k10_relat_1(k7_relat_1(C_35, A_34), B_36))=k4_xboole_0(A_34, k10_relat_1(C_35, B_36)) | ~v1_relat_1(C_35))), inference(superposition, [status(thm), theory('equality')], [c_111, c_6])).
% 1.95/1.28  tff(c_261, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k1_relat_1(k7_relat_1(B_53, A_52)))=k4_xboole_0(A_52, k10_relat_1(B_53, k9_relat_1(B_53, A_52))) | ~v1_relat_1(B_53) | ~v1_relat_1(k7_relat_1(B_53, A_52)) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_234, c_117])).
% 1.95/1.28  tff(c_276, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_103, c_261])).
% 1.95/1.28  tff(c_282, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_26, c_177, c_26, c_8, c_276])).
% 1.95/1.28  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_282])).
% 1.95/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.28  
% 1.95/1.28  Inference rules
% 1.95/1.28  ----------------------
% 1.95/1.28  #Ref     : 0
% 1.95/1.28  #Sup     : 62
% 1.95/1.28  #Fact    : 0
% 1.95/1.28  #Define  : 0
% 1.95/1.28  #Split   : 1
% 1.95/1.28  #Chain   : 0
% 1.95/1.28  #Close   : 0
% 1.95/1.28  
% 1.95/1.28  Ordering : KBO
% 1.95/1.28  
% 1.95/1.28  Simplification rules
% 1.95/1.28  ----------------------
% 1.95/1.28  #Subsume      : 0
% 1.95/1.28  #Demod        : 10
% 1.95/1.28  #Tautology    : 39
% 1.95/1.28  #SimpNegUnit  : 1
% 1.95/1.28  #BackRed      : 0
% 1.95/1.28  
% 1.95/1.28  #Partial instantiations: 0
% 1.95/1.28  #Strategies tried      : 1
% 1.95/1.28  
% 1.95/1.28  Timing (in seconds)
% 1.95/1.28  ----------------------
% 1.95/1.29  Preprocessing        : 0.28
% 1.95/1.29  Parsing              : 0.15
% 1.95/1.29  CNF conversion       : 0.02
% 1.95/1.29  Main loop            : 0.20
% 1.95/1.29  Inferencing          : 0.09
% 1.95/1.29  Reduction            : 0.05
% 1.95/1.29  Demodulation         : 0.04
% 1.95/1.29  BG Simplification    : 0.02
% 1.95/1.29  Subsumption          : 0.03
% 1.95/1.29  Abstraction          : 0.01
% 1.95/1.29  MUC search           : 0.00
% 1.95/1.29  Cooper               : 0.00
% 1.95/1.29  Total                : 0.51
% 1.95/1.29  Index Insertion      : 0.00
% 1.95/1.29  Index Deletion       : 0.00
% 1.95/1.29  Index Matching       : 0.00
% 1.95/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
