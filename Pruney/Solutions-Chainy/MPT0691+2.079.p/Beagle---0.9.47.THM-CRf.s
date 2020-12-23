%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:49 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 200 expanded)
%              Number of leaves         :   22 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   84 ( 374 expanded)
%              Number of equality atoms :   27 ( 105 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_7,A_6] :
      ( k2_relat_1(k7_relat_1(B_7,A_6)) = k9_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_113,plain,(
    ! [B_37,A_38] :
      ( k1_relat_1(k7_relat_1(B_37,A_38)) = A_38
      | ~ r1_tarski(A_38,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_126,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_113])).

tff(c_134,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_126])).

tff(c_16,plain,(
    ! [A_15] :
      ( k7_relat_1(A_15,k1_relat_1(A_15)) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_176,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_16])).

tff(c_243,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_176])).

tff(c_246,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_243])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_246])).

tff(c_252,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k3_xboole_0(k1_relat_1(B_12),A_11) = k1_relat_1(k7_relat_1(B_12,A_11))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_164,plain,(
    ! [A_11] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_11)) = k3_xboole_0('#skF_1',A_11)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_12])).

tff(c_466,plain,(
    ! [A_51] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_51)) = k3_xboole_0('#skF_1',A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_164])).

tff(c_38,plain,(
    ! [B_22,A_23] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_22,A_23)),A_23)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_41,plain,(
    ! [A_15] :
      ( r1_tarski(k1_relat_1(A_15),k1_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_38])).

tff(c_127,plain,(
    ! [A_15] :
      ( k1_relat_1(k7_relat_1(A_15,k1_relat_1(A_15))) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(resolution,[status(thm)],[c_41,c_113])).

tff(c_490,plain,
    ( k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_127])).

tff(c_537,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_134,c_134,c_490])).

tff(c_251,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_176])).

tff(c_8,plain,(
    ! [A_8] :
      ( k10_relat_1(A_8,k2_relat_1(A_8)) = k1_relat_1(A_8)
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [A_39,C_40,B_41] :
      ( k3_xboole_0(A_39,k10_relat_1(C_40,B_41)) = k10_relat_1(k7_relat_1(C_40,A_39),B_41)
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_554,plain,(
    ! [A_52,A_53] :
      ( k10_relat_1(k7_relat_1(A_52,A_53),k2_relat_1(A_52)) = k3_xboole_0(A_53,k1_relat_1(A_52))
      | ~ v1_relat_1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_135])).

tff(c_566,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_554])).

tff(c_576,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_252,c_537,c_134,c_566])).

tff(c_695,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_576])).

tff(c_706,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_695])).

tff(c_18,plain,(
    ! [A_16,C_18,B_17] :
      ( k3_xboole_0(A_16,k10_relat_1(C_18,B_17)) = k10_relat_1(k7_relat_1(C_18,A_16),B_17)
      | ~ v1_relat_1(C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_508,plain,(
    ! [A_51] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_51),A_51)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_10])).

tff(c_578,plain,(
    ! [A_54] : r1_tarski(k3_xboole_0('#skF_1',A_54),A_54) ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_508])).

tff(c_960,plain,(
    ! [C_70,B_71] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_70,'#skF_1'),B_71),k10_relat_1(C_70,B_71))
      | ~ v1_relat_1(C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_578])).

tff(c_967,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_706,c_960])).

tff(c_1000,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_967])).

tff(c_1002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_1000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:34:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.40  
% 2.65/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.65/1.40  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.65/1.40  
% 2.65/1.40  %Foreground sorts:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Background operators:
% 2.65/1.40  
% 2.65/1.40  
% 2.65/1.40  %Foreground operators:
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.40  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.65/1.40  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.65/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.40  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.65/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.65/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.65/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.65/1.40  
% 2.89/1.42  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.89/1.42  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.89/1.42  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.89/1.42  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.89/1.42  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.89/1.42  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.89/1.42  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.89/1.42  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.89/1.42  tff(f_65, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.89/1.42  tff(c_20, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.89/1.42  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.89/1.42  tff(c_6, plain, (![B_7, A_6]: (k2_relat_1(k7_relat_1(B_7, A_6))=k9_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.89/1.42  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.42  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.89/1.42  tff(c_113, plain, (![B_37, A_38]: (k1_relat_1(k7_relat_1(B_37, A_38))=A_38 | ~r1_tarski(A_38, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.89/1.42  tff(c_126, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_22, c_113])).
% 2.89/1.42  tff(c_134, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_126])).
% 2.89/1.42  tff(c_16, plain, (![A_15]: (k7_relat_1(A_15, k1_relat_1(A_15))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.42  tff(c_176, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_16])).
% 2.89/1.42  tff(c_243, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_176])).
% 2.89/1.42  tff(c_246, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_4, c_243])).
% 2.89/1.42  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_246])).
% 2.89/1.42  tff(c_252, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_176])).
% 2.89/1.42  tff(c_12, plain, (![B_12, A_11]: (k3_xboole_0(k1_relat_1(B_12), A_11)=k1_relat_1(k7_relat_1(B_12, A_11)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.89/1.42  tff(c_164, plain, (![A_11]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_11))=k3_xboole_0('#skF_1', A_11) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_134, c_12])).
% 2.89/1.42  tff(c_466, plain, (![A_51]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_51))=k3_xboole_0('#skF_1', A_51))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_164])).
% 2.89/1.42  tff(c_38, plain, (![B_22, A_23]: (r1_tarski(k1_relat_1(k7_relat_1(B_22, A_23)), A_23) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.42  tff(c_41, plain, (![A_15]: (r1_tarski(k1_relat_1(A_15), k1_relat_1(A_15)) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_16, c_38])).
% 2.89/1.42  tff(c_127, plain, (![A_15]: (k1_relat_1(k7_relat_1(A_15, k1_relat_1(A_15)))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(resolution, [status(thm)], [c_41, c_113])).
% 2.89/1.42  tff(c_490, plain, (k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_466, c_127])).
% 2.89/1.42  tff(c_537, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_134, c_134, c_490])).
% 2.89/1.42  tff(c_251, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_176])).
% 2.89/1.42  tff(c_8, plain, (![A_8]: (k10_relat_1(A_8, k2_relat_1(A_8))=k1_relat_1(A_8) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.89/1.42  tff(c_135, plain, (![A_39, C_40, B_41]: (k3_xboole_0(A_39, k10_relat_1(C_40, B_41))=k10_relat_1(k7_relat_1(C_40, A_39), B_41) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.42  tff(c_554, plain, (![A_52, A_53]: (k10_relat_1(k7_relat_1(A_52, A_53), k2_relat_1(A_52))=k3_xboole_0(A_53, k1_relat_1(A_52)) | ~v1_relat_1(A_52) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_8, c_135])).
% 2.89/1.42  tff(c_566, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_554])).
% 2.89/1.42  tff(c_576, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_252, c_537, c_134, c_566])).
% 2.89/1.42  tff(c_695, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_6, c_576])).
% 2.89/1.42  tff(c_706, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_695])).
% 2.89/1.42  tff(c_18, plain, (![A_16, C_18, B_17]: (k3_xboole_0(A_16, k10_relat_1(C_18, B_17))=k10_relat_1(k7_relat_1(C_18, A_16), B_17) | ~v1_relat_1(C_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.89/1.42  tff(c_10, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.89/1.42  tff(c_508, plain, (![A_51]: (r1_tarski(k3_xboole_0('#skF_1', A_51), A_51) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_466, c_10])).
% 2.89/1.42  tff(c_578, plain, (![A_54]: (r1_tarski(k3_xboole_0('#skF_1', A_54), A_54))), inference(demodulation, [status(thm), theory('equality')], [c_252, c_508])).
% 2.89/1.42  tff(c_960, plain, (![C_70, B_71]: (r1_tarski(k10_relat_1(k7_relat_1(C_70, '#skF_1'), B_71), k10_relat_1(C_70, B_71)) | ~v1_relat_1(C_70))), inference(superposition, [status(thm), theory('equality')], [c_18, c_578])).
% 2.89/1.42  tff(c_967, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_706, c_960])).
% 2.89/1.42  tff(c_1000, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_967])).
% 2.89/1.42  tff(c_1002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_1000])).
% 2.89/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.89/1.42  
% 2.89/1.42  Inference rules
% 2.89/1.42  ----------------------
% 2.89/1.42  #Ref     : 0
% 2.89/1.42  #Sup     : 231
% 2.89/1.42  #Fact    : 0
% 2.89/1.42  #Define  : 0
% 2.89/1.42  #Split   : 1
% 2.89/1.42  #Chain   : 0
% 2.89/1.42  #Close   : 0
% 2.89/1.42  
% 2.89/1.42  Ordering : KBO
% 2.89/1.42  
% 2.89/1.42  Simplification rules
% 2.89/1.42  ----------------------
% 2.89/1.42  #Subsume      : 19
% 2.89/1.42  #Demod        : 162
% 2.89/1.42  #Tautology    : 91
% 2.89/1.42  #SimpNegUnit  : 1
% 2.89/1.42  #BackRed      : 0
% 2.89/1.42  
% 2.89/1.42  #Partial instantiations: 0
% 2.89/1.42  #Strategies tried      : 1
% 2.89/1.42  
% 2.89/1.42  Timing (in seconds)
% 2.89/1.42  ----------------------
% 2.89/1.42  Preprocessing        : 0.29
% 2.89/1.42  Parsing              : 0.16
% 2.89/1.42  CNF conversion       : 0.02
% 2.89/1.42  Main loop            : 0.36
% 2.89/1.42  Inferencing          : 0.14
% 2.89/1.42  Reduction            : 0.10
% 2.89/1.42  Demodulation         : 0.08
% 2.89/1.42  BG Simplification    : 0.02
% 2.89/1.42  Subsumption          : 0.07
% 2.89/1.42  Abstraction          : 0.02
% 2.89/1.42  MUC search           : 0.00
% 2.89/1.42  Cooper               : 0.00
% 2.89/1.42  Total                : 0.67
% 2.89/1.42  Index Insertion      : 0.00
% 2.89/1.42  Index Deletion       : 0.00
% 2.89/1.42  Index Matching       : 0.00
% 2.89/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
