%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:44 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   52 (  90 expanded)
%              Number of leaves         :   23 (  39 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 ( 147 expanded)
%              Number of equality atoms :   21 (  39 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_28,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_26,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_124,plain,(
    ! [B_36,A_37] :
      ( k1_relat_1(k7_relat_1(B_36,A_37)) = A_37
      | ~ r1_tarski(A_37,k1_relat_1(B_36))
      | ~ v1_relat_1(B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_135,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_124])).

tff(c_144,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_135])).

tff(c_14,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_152,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_14])).

tff(c_188,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_191,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_188])).

tff(c_195,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_191])).

tff(c_197,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_396,plain,(
    ! [A_58,C_59,B_60] :
      ( k9_relat_1(k7_relat_1(A_58,C_59),B_60) = k9_relat_1(A_58,B_60)
      | ~ r1_tarski(B_60,C_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_196,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_402,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_196])).

tff(c_419,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_8,c_402])).

tff(c_18,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_427,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_419,c_18])).

tff(c_431,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_144,c_427])).

tff(c_209,plain,(
    ! [A_43,C_44,B_45] :
      ( k3_xboole_0(A_43,k10_relat_1(C_44,B_45)) = k10_relat_1(k7_relat_1(C_44,A_43),B_45)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_33,plain,(
    ! [B_26,A_27] : k3_xboole_0(B_26,A_27) = k3_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_48,plain,(
    ! [B_26,A_27] : r1_tarski(k3_xboole_0(B_26,A_27),A_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_10])).

tff(c_224,plain,(
    ! [C_44,A_43,B_45] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_44,A_43),B_45),k10_relat_1(C_44,B_45))
      | ~ v1_relat_1(C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_209,c_48])).

tff(c_484,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_224])).

tff(c_499,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_484])).

tff(c_501,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_499])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:57:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.30  
% 2.39/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.30  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.39/1.30  
% 2.39/1.30  %Foreground sorts:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Background operators:
% 2.39/1.30  
% 2.39/1.30  
% 2.39/1.30  %Foreground operators:
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.39/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.39/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.39/1.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.39/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.30  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.39/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.39/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.39/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.39/1.30  
% 2.39/1.32  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.39/1.32  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.39/1.32  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.39/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.39/1.32  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.32  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.39/1.32  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.39/1.32  tff(f_64, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.39/1.32  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.39/1.32  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.39/1.32  tff(c_24, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.39/1.32  tff(c_28, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.39/1.32  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.39/1.32  tff(c_26, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.39/1.32  tff(c_124, plain, (![B_36, A_37]: (k1_relat_1(k7_relat_1(B_36, A_37))=A_37 | ~r1_tarski(A_37, k1_relat_1(B_36)) | ~v1_relat_1(B_36))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.39/1.32  tff(c_135, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_124])).
% 2.39/1.32  tff(c_144, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_135])).
% 2.39/1.32  tff(c_14, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.39/1.32  tff(c_152, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_14])).
% 2.39/1.32  tff(c_188, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_152])).
% 2.39/1.32  tff(c_191, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_188])).
% 2.39/1.32  tff(c_195, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_191])).
% 2.39/1.32  tff(c_197, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_152])).
% 2.39/1.32  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.39/1.32  tff(c_396, plain, (![A_58, C_59, B_60]: (k9_relat_1(k7_relat_1(A_58, C_59), B_60)=k9_relat_1(A_58, B_60) | ~r1_tarski(B_60, C_59) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.39/1.32  tff(c_196, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_152])).
% 2.39/1.32  tff(c_402, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_396, c_196])).
% 2.39/1.32  tff(c_419, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_8, c_402])).
% 2.39/1.32  tff(c_18, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.39/1.32  tff(c_427, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_419, c_18])).
% 2.39/1.32  tff(c_431, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_197, c_144, c_427])).
% 2.39/1.32  tff(c_209, plain, (![A_43, C_44, B_45]: (k3_xboole_0(A_43, k10_relat_1(C_44, B_45))=k10_relat_1(k7_relat_1(C_44, A_43), B_45) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.39/1.32  tff(c_33, plain, (![B_26, A_27]: (k3_xboole_0(B_26, A_27)=k3_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.32  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.39/1.32  tff(c_48, plain, (![B_26, A_27]: (r1_tarski(k3_xboole_0(B_26, A_27), A_27))), inference(superposition, [status(thm), theory('equality')], [c_33, c_10])).
% 2.39/1.32  tff(c_224, plain, (![C_44, A_43, B_45]: (r1_tarski(k10_relat_1(k7_relat_1(C_44, A_43), B_45), k10_relat_1(C_44, B_45)) | ~v1_relat_1(C_44))), inference(superposition, [status(thm), theory('equality')], [c_209, c_48])).
% 2.39/1.32  tff(c_484, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_431, c_224])).
% 2.39/1.32  tff(c_499, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_484])).
% 2.39/1.32  tff(c_501, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_499])).
% 2.39/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.32  
% 2.39/1.32  Inference rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Ref     : 0
% 2.39/1.32  #Sup     : 121
% 2.39/1.32  #Fact    : 0
% 2.39/1.32  #Define  : 0
% 2.39/1.32  #Split   : 2
% 2.39/1.32  #Chain   : 0
% 2.39/1.32  #Close   : 0
% 2.39/1.32  
% 2.39/1.32  Ordering : KBO
% 2.39/1.32  
% 2.39/1.32  Simplification rules
% 2.39/1.32  ----------------------
% 2.39/1.32  #Subsume      : 14
% 2.39/1.32  #Demod        : 37
% 2.39/1.32  #Tautology    : 49
% 2.39/1.32  #SimpNegUnit  : 1
% 2.39/1.32  #BackRed      : 1
% 2.39/1.32  
% 2.39/1.32  #Partial instantiations: 0
% 2.39/1.32  #Strategies tried      : 1
% 2.39/1.32  
% 2.39/1.32  Timing (in seconds)
% 2.39/1.32  ----------------------
% 2.39/1.32  Preprocessing        : 0.29
% 2.39/1.32  Parsing              : 0.15
% 2.39/1.32  CNF conversion       : 0.02
% 2.39/1.32  Main loop            : 0.27
% 2.39/1.32  Inferencing          : 0.10
% 2.39/1.32  Reduction            : 0.09
% 2.39/1.32  Demodulation         : 0.07
% 2.39/1.32  BG Simplification    : 0.02
% 2.39/1.32  Subsumption          : 0.06
% 2.39/1.32  Abstraction          : 0.02
% 2.39/1.32  MUC search           : 0.00
% 2.39/1.32  Cooper               : 0.00
% 2.39/1.32  Total                : 0.59
% 2.39/1.32  Index Insertion      : 0.00
% 2.39/1.32  Index Deletion       : 0.00
% 2.39/1.32  Index Matching       : 0.00
% 2.39/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
