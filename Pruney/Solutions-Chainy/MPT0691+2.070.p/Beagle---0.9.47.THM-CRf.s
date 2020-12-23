%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:48 EST 2020

% Result     : Theorem 24.16s
% Output     : CNFRefutation 24.24s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 371 expanded)
%              Number of leaves         :   24 ( 132 expanded)
%              Depth                    :   16
%              Number of atoms          :   91 ( 747 expanded)
%              Number of equality atoms :   31 ( 209 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_102,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_18,plain,(
    ! [B_17,A_16] :
      ( k2_relat_1(k7_relat_1(B_17,A_16)) = k9_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [A_14,B_15] :
      ( v1_relat_1(k7_relat_1(A_14,B_15))
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_275,plain,(
    ! [B_73,A_74] :
      ( k1_relat_1(k7_relat_1(B_73,A_74)) = A_74
      | ~ r1_tarski(A_74,k1_relat_1(B_73))
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_288,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_275])).

tff(c_300,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_288])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_385,plain,(
    ! [B_76] :
      ( k1_relat_1(k7_relat_1(B_76,k1_relat_1(B_76))) = k1_relat_1(B_76)
      | ~ v1_relat_1(B_76) ) ),
    inference(resolution,[status(thm)],[c_6,c_275])).

tff(c_432,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_385])).

tff(c_443,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_300,c_432])).

tff(c_13828,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_443])).

tff(c_13831,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_13828])).

tff(c_13835,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_13831])).

tff(c_13837,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_443])).

tff(c_145,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_174,plain,(
    ! [B_61] :
      ( k7_relat_1(B_61,k1_relat_1(B_61)) = B_61
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_6,c_145])).

tff(c_314,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_174])).

tff(c_16580,plain,(
    k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13837,c_314])).

tff(c_16619,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16580,c_18])).

tff(c_16655,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13837,c_16619])).

tff(c_110,plain,(
    ! [B_54,A_55] :
      ( k2_relat_1(k7_relat_1(B_54,A_55)) = k9_relat_1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_20] :
      ( k10_relat_1(A_20,k2_relat_1(A_20)) = k1_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,(
    ! [B_54,A_55] :
      ( k10_relat_1(k7_relat_1(B_54,A_55),k9_relat_1(B_54,A_55)) = k1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(B_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_22])).

tff(c_16667,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_16655,c_116])).

tff(c_16671,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13837,c_13837,c_16580,c_300,c_16580,c_16580,c_16667])).

tff(c_16749,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16671])).

tff(c_16792,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_16749])).

tff(c_34,plain,(
    ! [A_32,C_34,B_33] :
      ( k3_xboole_0(A_32,k10_relat_1(C_34,B_33)) = k10_relat_1(k7_relat_1(C_34,A_32),B_33)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_28,plain,(
    ! [B_27,A_26] :
      ( k3_xboole_0(k1_relat_1(B_27),A_26) = k1_relat_1(k7_relat_1(B_27,A_26))
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_308,plain,(
    ! [A_26] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_26)) = k3_xboole_0('#skF_1',A_26)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_300,c_28])).

tff(c_20911,plain,(
    ! [A_466] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_466)) = k3_xboole_0('#skF_1',A_466) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13837,c_308])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_21027,plain,(
    ! [A_466] :
      ( r1_tarski(k3_xboole_0('#skF_1',A_466),A_466)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20911,c_26])).

tff(c_21545,plain,(
    ! [A_473] : r1_tarski(k3_xboole_0('#skF_1',A_473),A_473) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13837,c_21027])).

tff(c_86641,plain,(
    ! [C_1029,B_1030] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_1029,'#skF_1'),B_1030),k10_relat_1(C_1029,B_1030))
      | ~ v1_relat_1(C_1029) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_21545])).

tff(c_86712,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16792,c_86641])).

tff(c_86821,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_86712])).

tff(c_86823,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_86821])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:27:00 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.16/14.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.16/14.29  
% 24.16/14.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.16/14.29  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 24.16/14.29  
% 24.16/14.29  %Foreground sorts:
% 24.16/14.29  
% 24.16/14.29  
% 24.16/14.29  %Background operators:
% 24.16/14.29  
% 24.16/14.29  
% 24.16/14.29  %Foreground operators:
% 24.16/14.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.16/14.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 24.16/14.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.16/14.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 24.16/14.29  tff('#skF_2', type, '#skF_2': $i).
% 24.16/14.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 24.16/14.29  tff('#skF_1', type, '#skF_1': $i).
% 24.16/14.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.16/14.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 24.16/14.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.16/14.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.16/14.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.16/14.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.16/14.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.16/14.29  
% 24.24/14.31  tff(f_102, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 24.24/14.31  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 24.24/14.31  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 24.24/14.31  tff(f_85, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 24.24/14.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.24/14.31  tff(f_91, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 24.24/14.31  tff(f_65, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 24.24/14.31  tff(f_95, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 24.24/14.31  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 24.24/14.31  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 24.24/14.31  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.24/14.31  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.24/14.31  tff(c_18, plain, (![B_17, A_16]: (k2_relat_1(k7_relat_1(B_17, A_16))=k9_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.24/14.31  tff(c_16, plain, (![A_14, B_15]: (v1_relat_1(k7_relat_1(A_14, B_15)) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_53])).
% 24.24/14.31  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 24.24/14.31  tff(c_275, plain, (![B_73, A_74]: (k1_relat_1(k7_relat_1(B_73, A_74))=A_74 | ~r1_tarski(A_74, k1_relat_1(B_73)) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_85])).
% 24.24/14.31  tff(c_288, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_275])).
% 24.24/14.31  tff(c_300, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_288])).
% 24.24/14.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.24/14.31  tff(c_385, plain, (![B_76]: (k1_relat_1(k7_relat_1(B_76, k1_relat_1(B_76)))=k1_relat_1(B_76) | ~v1_relat_1(B_76))), inference(resolution, [status(thm)], [c_6, c_275])).
% 24.24/14.31  tff(c_432, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_385])).
% 24.24/14.31  tff(c_443, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_300, c_432])).
% 24.24/14.31  tff(c_13828, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_443])).
% 24.24/14.31  tff(c_13831, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_13828])).
% 24.24/14.31  tff(c_13835, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_13831])).
% 24.24/14.31  tff(c_13837, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_443])).
% 24.24/14.31  tff(c_145, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_91])).
% 24.24/14.31  tff(c_174, plain, (![B_61]: (k7_relat_1(B_61, k1_relat_1(B_61))=B_61 | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_6, c_145])).
% 24.24/14.31  tff(c_314, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_300, c_174])).
% 24.24/14.31  tff(c_16580, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13837, c_314])).
% 24.24/14.31  tff(c_16619, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16580, c_18])).
% 24.24/14.31  tff(c_16655, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_13837, c_16619])).
% 24.24/14.31  tff(c_110, plain, (![B_54, A_55]: (k2_relat_1(k7_relat_1(B_54, A_55))=k9_relat_1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_57])).
% 24.24/14.31  tff(c_22, plain, (![A_20]: (k10_relat_1(A_20, k2_relat_1(A_20))=k1_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 24.24/14.31  tff(c_116, plain, (![B_54, A_55]: (k10_relat_1(k7_relat_1(B_54, A_55), k9_relat_1(B_54, A_55))=k1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(B_54))), inference(superposition, [status(thm), theory('equality')], [c_110, c_22])).
% 24.24/14.31  tff(c_16667, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_16655, c_116])).
% 24.24/14.31  tff(c_16671, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_13837, c_13837, c_16580, c_300, c_16580, c_16580, c_16667])).
% 24.24/14.31  tff(c_16749, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_18, c_16671])).
% 24.24/14.31  tff(c_16792, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_16749])).
% 24.24/14.31  tff(c_34, plain, (![A_32, C_34, B_33]: (k3_xboole_0(A_32, k10_relat_1(C_34, B_33))=k10_relat_1(k7_relat_1(C_34, A_32), B_33) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_95])).
% 24.24/14.31  tff(c_28, plain, (![B_27, A_26]: (k3_xboole_0(k1_relat_1(B_27), A_26)=k1_relat_1(k7_relat_1(B_27, A_26)) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_79])).
% 24.24/14.31  tff(c_308, plain, (![A_26]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_26))=k3_xboole_0('#skF_1', A_26) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_300, c_28])).
% 24.24/14.31  tff(c_20911, plain, (![A_466]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_466))=k3_xboole_0('#skF_1', A_466))), inference(demodulation, [status(thm), theory('equality')], [c_13837, c_308])).
% 24.24/14.31  tff(c_26, plain, (![B_25, A_24]: (r1_tarski(k1_relat_1(k7_relat_1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 24.24/14.31  tff(c_21027, plain, (![A_466]: (r1_tarski(k3_xboole_0('#skF_1', A_466), A_466) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_20911, c_26])).
% 24.24/14.31  tff(c_21545, plain, (![A_473]: (r1_tarski(k3_xboole_0('#skF_1', A_473), A_473))), inference(demodulation, [status(thm), theory('equality')], [c_13837, c_21027])).
% 24.24/14.31  tff(c_86641, plain, (![C_1029, B_1030]: (r1_tarski(k10_relat_1(k7_relat_1(C_1029, '#skF_1'), B_1030), k10_relat_1(C_1029, B_1030)) | ~v1_relat_1(C_1029))), inference(superposition, [status(thm), theory('equality')], [c_34, c_21545])).
% 24.24/14.31  tff(c_86712, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16792, c_86641])).
% 24.24/14.31  tff(c_86821, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_86712])).
% 24.24/14.31  tff(c_86823, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_86821])).
% 24.24/14.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 24.24/14.31  
% 24.24/14.31  Inference rules
% 24.24/14.31  ----------------------
% 24.24/14.31  #Ref     : 0
% 24.24/14.31  #Sup     : 21449
% 24.24/14.31  #Fact    : 0
% 24.24/14.31  #Define  : 0
% 24.24/14.31  #Split   : 8
% 24.24/14.31  #Chain   : 0
% 24.24/14.31  #Close   : 0
% 24.24/14.31  
% 24.24/14.31  Ordering : KBO
% 24.24/14.31  
% 24.24/14.31  Simplification rules
% 24.24/14.31  ----------------------
% 24.24/14.31  #Subsume      : 3923
% 24.24/14.31  #Demod        : 12763
% 24.24/14.31  #Tautology    : 9165
% 24.24/14.31  #SimpNegUnit  : 13
% 24.24/14.31  #BackRed      : 24
% 24.24/14.31  
% 24.24/14.31  #Partial instantiations: 0
% 24.24/14.31  #Strategies tried      : 1
% 24.24/14.31  
% 24.24/14.31  Timing (in seconds)
% 24.24/14.31  ----------------------
% 24.24/14.31  Preprocessing        : 0.30
% 24.24/14.31  Parsing              : 0.16
% 24.24/14.31  CNF conversion       : 0.02
% 24.24/14.31  Main loop            : 13.20
% 24.24/14.31  Inferencing          : 1.61
% 24.24/14.31  Reduction            : 6.53
% 24.24/14.31  Demodulation         : 5.78
% 24.24/14.31  BG Simplification    : 0.21
% 24.24/14.31  Subsumption          : 4.27
% 24.24/14.31  Abstraction          : 0.34
% 24.24/14.31  MUC search           : 0.00
% 24.24/14.31  Cooper               : 0.00
% 24.24/14.31  Total                : 13.53
% 24.24/14.31  Index Insertion      : 0.00
% 24.24/14.31  Index Deletion       : 0.00
% 24.24/14.31  Index Matching       : 0.00
% 24.24/14.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
