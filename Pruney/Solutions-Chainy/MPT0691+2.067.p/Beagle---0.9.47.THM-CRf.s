%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:48 EST 2020

% Result     : Theorem 4.21s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 212 expanded)
%              Number of leaves         :   24 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :   88 ( 395 expanded)
%              Number of equality atoms :   30 ( 116 expanded)
%              Maximal formula depth    :    7 (   3 average)
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

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k7_relat_1(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_222,plain,(
    ! [B_52,A_53] :
      ( k1_relat_1(k7_relat_1(B_52,A_53)) = A_53
      | ~ r1_tarski(A_53,k1_relat_1(B_52))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_235,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_246,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_235])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_38,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_46,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_38])).

tff(c_107,plain,(
    ! [B_44,A_45] :
      ( k3_xboole_0(k1_relat_1(B_44),A_45) = k1_relat_1(k7_relat_1(B_44,A_45))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_121,plain,(
    ! [B_44] :
      ( k1_relat_1(k7_relat_1(B_44,k1_relat_1(B_44))) = k1_relat_1(B_44)
      | ~ v1_relat_1(B_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_107])).

tff(c_254,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_121])).

tff(c_266,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_254])).

tff(c_372,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_266])).

tff(c_375,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_372])).

tff(c_379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_375])).

tff(c_381,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_266])).

tff(c_16,plain,(
    ! [A_13] :
      ( k9_relat_1(A_13,k1_relat_1(A_13)) = k2_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_260,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_16])).

tff(c_684,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_260])).

tff(c_18,plain,(
    ! [A_14,C_18,B_17] :
      ( k9_relat_1(k7_relat_1(A_14,C_18),B_17) = k9_relat_1(A_14,B_17)
      | ~ r1_tarski(B_17,C_18)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_688,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_684,c_18])).

tff(c_695,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_688])).

tff(c_20,plain,(
    ! [A_19] :
      ( k10_relat_1(A_19,k2_relat_1(A_19)) = k1_relat_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_746,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_695,c_20])).

tff(c_750,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_246,c_746])).

tff(c_28,plain,(
    ! [A_26,C_28,B_27] :
      ( k3_xboole_0(A_26,k10_relat_1(C_28,B_27)) = k10_relat_1(k7_relat_1(C_28,A_26),B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_24,plain,(
    ! [B_23,A_22] :
      ( k3_xboole_0(k1_relat_1(B_23),A_22) = k1_relat_1(k7_relat_1(B_23,A_22))
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_257,plain,(
    ! [A_22] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_22)) = k3_xboole_0('#skF_1',A_22)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_246,c_24])).

tff(c_610,plain,(
    ! [A_75] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_75)) = k3_xboole_0('#skF_1',A_75) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_257])).

tff(c_22,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_21,A_20)),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_647,plain,(
    ! [A_75] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_75),A_75)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_610,c_22])).

tff(c_699,plain,(
    ! [A_76] : r1_tarski(k3_xboole_0('#skF_1',A_76),A_76) ),
    inference(demodulation,[status(thm),theory(equality)],[c_381,c_647])).

tff(c_1515,plain,(
    ! [C_99,B_100] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_99,'#skF_1'),B_100),k10_relat_1(C_99,B_100))
      | ~ v1_relat_1(C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_699])).

tff(c_1536,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_750,c_1515])).

tff(c_1568,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1536])).

tff(c_1570,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1568])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:30:05 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.21/2.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/2.10  
% 4.21/2.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.21/2.10  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.21/2.10  
% 4.21/2.10  %Foreground sorts:
% 4.21/2.10  
% 4.21/2.10  
% 4.21/2.10  %Background operators:
% 4.21/2.10  
% 4.21/2.10  
% 4.21/2.10  %Foreground operators:
% 4.21/2.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.21/2.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.21/2.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.21/2.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.21/2.10  tff('#skF_2', type, '#skF_2': $i).
% 4.21/2.10  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.21/2.10  tff('#skF_1', type, '#skF_1': $i).
% 4.21/2.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.21/2.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.21/2.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.21/2.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.21/2.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.21/2.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.21/2.10  
% 4.45/2.12  tff(f_91, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 4.45/2.12  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.45/2.12  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 4.45/2.12  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.45/2.12  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.45/2.12  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 4.45/2.12  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 4.45/2.12  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 4.45/2.12  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 4.45/2.12  tff(f_84, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 4.45/2.12  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 4.45/2.12  tff(c_30, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/2.12  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/2.12  tff(c_12, plain, (![A_8, B_9]: (v1_relat_1(k7_relat_1(A_8, B_9)) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.45/2.12  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.45/2.12  tff(c_222, plain, (![B_52, A_53]: (k1_relat_1(k7_relat_1(B_52, A_53))=A_53 | ~r1_tarski(A_53, k1_relat_1(B_52)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.45/2.12  tff(c_235, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_222])).
% 4.45/2.12  tff(c_246, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_235])).
% 4.45/2.12  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.45/2.12  tff(c_38, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/2.12  tff(c_46, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_38])).
% 4.45/2.12  tff(c_107, plain, (![B_44, A_45]: (k3_xboole_0(k1_relat_1(B_44), A_45)=k1_relat_1(k7_relat_1(B_44, A_45)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.45/2.12  tff(c_121, plain, (![B_44]: (k1_relat_1(k7_relat_1(B_44, k1_relat_1(B_44)))=k1_relat_1(B_44) | ~v1_relat_1(B_44))), inference(superposition, [status(thm), theory('equality')], [c_46, c_107])).
% 4.45/2.12  tff(c_254, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_121])).
% 4.45/2.12  tff(c_266, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_254])).
% 4.45/2.12  tff(c_372, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_266])).
% 4.45/2.12  tff(c_375, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_372])).
% 4.45/2.12  tff(c_379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_375])).
% 4.45/2.12  tff(c_381, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_266])).
% 4.45/2.12  tff(c_16, plain, (![A_13]: (k9_relat_1(A_13, k1_relat_1(A_13))=k2_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.45/2.12  tff(c_260, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_246, c_16])).
% 4.45/2.12  tff(c_684, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_260])).
% 4.45/2.12  tff(c_18, plain, (![A_14, C_18, B_17]: (k9_relat_1(k7_relat_1(A_14, C_18), B_17)=k9_relat_1(A_14, B_17) | ~r1_tarski(B_17, C_18) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.45/2.12  tff(c_688, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_684, c_18])).
% 4.45/2.12  tff(c_695, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_688])).
% 4.45/2.12  tff(c_20, plain, (![A_19]: (k10_relat_1(A_19, k2_relat_1(A_19))=k1_relat_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.45/2.12  tff(c_746, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_695, c_20])).
% 4.45/2.12  tff(c_750, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_381, c_246, c_746])).
% 4.45/2.12  tff(c_28, plain, (![A_26, C_28, B_27]: (k3_xboole_0(A_26, k10_relat_1(C_28, B_27))=k10_relat_1(k7_relat_1(C_28, A_26), B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.45/2.12  tff(c_24, plain, (![B_23, A_22]: (k3_xboole_0(k1_relat_1(B_23), A_22)=k1_relat_1(k7_relat_1(B_23, A_22)) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.45/2.12  tff(c_257, plain, (![A_22]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_22))=k3_xboole_0('#skF_1', A_22) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_246, c_24])).
% 4.45/2.12  tff(c_610, plain, (![A_75]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_75))=k3_xboole_0('#skF_1', A_75))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_257])).
% 4.45/2.12  tff(c_22, plain, (![B_21, A_20]: (r1_tarski(k1_relat_1(k7_relat_1(B_21, A_20)), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.45/2.12  tff(c_647, plain, (![A_75]: (r1_tarski(k3_xboole_0('#skF_1', A_75), A_75) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_610, c_22])).
% 4.45/2.12  tff(c_699, plain, (![A_76]: (r1_tarski(k3_xboole_0('#skF_1', A_76), A_76))), inference(demodulation, [status(thm), theory('equality')], [c_381, c_647])).
% 4.45/2.12  tff(c_1515, plain, (![C_99, B_100]: (r1_tarski(k10_relat_1(k7_relat_1(C_99, '#skF_1'), B_100), k10_relat_1(C_99, B_100)) | ~v1_relat_1(C_99))), inference(superposition, [status(thm), theory('equality')], [c_28, c_699])).
% 4.45/2.12  tff(c_1536, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_750, c_1515])).
% 4.45/2.12  tff(c_1568, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1536])).
% 4.45/2.12  tff(c_1570, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1568])).
% 4.45/2.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.45/2.12  
% 4.45/2.12  Inference rules
% 4.45/2.12  ----------------------
% 4.45/2.12  #Ref     : 0
% 4.45/2.12  #Sup     : 358
% 4.45/2.12  #Fact    : 0
% 4.45/2.12  #Define  : 0
% 4.45/2.12  #Split   : 2
% 4.45/2.12  #Chain   : 0
% 4.45/2.12  #Close   : 0
% 4.45/2.12  
% 4.45/2.12  Ordering : KBO
% 4.45/2.12  
% 4.45/2.12  Simplification rules
% 4.45/2.12  ----------------------
% 4.45/2.12  #Subsume      : 54
% 4.45/2.12  #Demod        : 234
% 4.45/2.12  #Tautology    : 127
% 4.45/2.12  #SimpNegUnit  : 1
% 4.45/2.12  #BackRed      : 1
% 4.45/2.12  
% 4.45/2.12  #Partial instantiations: 0
% 4.45/2.12  #Strategies tried      : 1
% 4.45/2.12  
% 4.45/2.12  Timing (in seconds)
% 4.45/2.12  ----------------------
% 4.45/2.13  Preprocessing        : 0.49
% 4.45/2.13  Parsing              : 0.26
% 4.45/2.13  CNF conversion       : 0.03
% 4.45/2.13  Main loop            : 0.75
% 4.45/2.13  Inferencing          : 0.27
% 4.45/2.13  Reduction            : 0.23
% 4.45/2.13  Demodulation         : 0.17
% 4.45/2.13  BG Simplification    : 0.04
% 4.45/2.13  Subsumption          : 0.16
% 4.45/2.13  Abstraction          : 0.04
% 4.45/2.13  MUC search           : 0.00
% 4.45/2.13  Cooper               : 0.00
% 4.45/2.13  Total                : 1.29
% 4.45/2.13  Index Insertion      : 0.00
% 4.45/2.13  Index Deletion       : 0.00
% 4.45/2.13  Index Matching       : 0.00
% 4.45/2.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
