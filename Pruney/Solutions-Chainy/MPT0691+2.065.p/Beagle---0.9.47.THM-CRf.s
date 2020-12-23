%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:48 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   28 (  51 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 195 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

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

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_81,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_30])).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_77,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_65])).

tff(c_39,plain,(
    ! [A_30,B_31] :
      ( k3_xboole_0(A_30,B_31) = A_30
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_51,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_39])).

tff(c_102,plain,(
    ! [A_37,B_38] : k5_xboole_0(A_37,k3_xboole_0(A_37,B_38)) = k4_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_114,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_51,c_102])).

tff(c_118,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_77,c_114])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_205,plain,(
    ! [B_49,A_50] :
      ( k1_relat_1(k7_relat_1(B_49,A_50)) = A_50
      | ~ r1_tarski(A_50,k1_relat_1(B_49))
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_212,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_205])).

tff(c_220,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_212])).

tff(c_24,plain,(
    ! [B_19,A_18] :
      ( k3_xboole_0(k1_relat_1(B_19),A_18) = k1_relat_1(k7_relat_1(B_19,A_18))
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_228,plain,(
    ! [A_18] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_18)) = k3_xboole_0('#skF_1',A_18)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_24])).

tff(c_263,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_228])).

tff(c_266,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_16,c_263])).

tff(c_270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_266])).

tff(c_272,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_228])).

tff(c_407,plain,(
    ! [A_63,C_64,B_65] :
      ( k9_relat_1(k7_relat_1(A_63,C_64),B_65) = k9_relat_1(A_63,B_65)
      | ~ r1_tarski(B_65,C_64)
      | ~ v1_relat_1(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_11] :
      ( k9_relat_1(A_11,k1_relat_1(A_11)) = k2_relat_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_231,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_18])).

tff(c_381,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_231])).

tff(c_413,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_407,c_381])).

tff(c_430,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_6,c_413])).

tff(c_22,plain,(
    ! [A_17] :
      ( k10_relat_1(A_17,k2_relat_1(A_17)) = k1_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_438,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_22])).

tff(c_442,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_220,c_438])).

tff(c_317,plain,(
    ! [A_55,C_56,B_57] :
      ( k3_xboole_0(A_55,k10_relat_1(C_56,B_57)) = k10_relat_1(k7_relat_1(C_56,A_55),B_57)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_603,plain,(
    ! [A_72,C_73,B_74] :
      ( k5_xboole_0(A_72,k10_relat_1(k7_relat_1(C_73,A_72),B_74)) = k4_xboole_0(A_72,k10_relat_1(C_73,B_74))
      | ~ v1_relat_1(C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_12])).

tff(c_621,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_603])).

tff(c_637,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_118,c_621])).

tff(c_639,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_81,c_637])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:53:05 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  
% 2.80/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.49  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.80/1.49  
% 2.80/1.49  %Foreground sorts:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Background operators:
% 2.80/1.49  
% 2.80/1.49  
% 2.80/1.49  %Foreground operators:
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.49  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.49  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.80/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.49  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.80/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.49  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.80/1.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.49  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.49  
% 2.80/1.51  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.80/1.51  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.80/1.51  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.80/1.51  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.80/1.51  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.51  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.80/1.51  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.80/1.51  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.80/1.51  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 2.80/1.51  tff(f_49, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.80/1.51  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.80/1.51  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.80/1.51  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.51  tff(c_30, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.51  tff(c_81, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_30])).
% 2.80/1.51  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.51  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.51  tff(c_65, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.51  tff(c_77, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_65])).
% 2.80/1.51  tff(c_39, plain, (![A_30, B_31]: (k3_xboole_0(A_30, B_31)=A_30 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.80/1.51  tff(c_51, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_39])).
% 2.80/1.51  tff(c_102, plain, (![A_37, B_38]: (k5_xboole_0(A_37, k3_xboole_0(A_37, B_38))=k4_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.51  tff(c_114, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_51, c_102])).
% 2.80/1.51  tff(c_118, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_77, c_114])).
% 2.80/1.51  tff(c_16, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.80/1.51  tff(c_32, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.80/1.51  tff(c_205, plain, (![B_49, A_50]: (k1_relat_1(k7_relat_1(B_49, A_50))=A_50 | ~r1_tarski(A_50, k1_relat_1(B_49)) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.51  tff(c_212, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_32, c_205])).
% 2.80/1.51  tff(c_220, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_212])).
% 2.80/1.51  tff(c_24, plain, (![B_19, A_18]: (k3_xboole_0(k1_relat_1(B_19), A_18)=k1_relat_1(k7_relat_1(B_19, A_18)) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.80/1.51  tff(c_228, plain, (![A_18]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_18))=k3_xboole_0('#skF_1', A_18) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_220, c_24])).
% 2.80/1.51  tff(c_263, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_228])).
% 2.80/1.51  tff(c_266, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_16, c_263])).
% 2.80/1.51  tff(c_270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_266])).
% 2.80/1.51  tff(c_272, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_228])).
% 2.80/1.51  tff(c_407, plain, (![A_63, C_64, B_65]: (k9_relat_1(k7_relat_1(A_63, C_64), B_65)=k9_relat_1(A_63, B_65) | ~r1_tarski(B_65, C_64) | ~v1_relat_1(A_63))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.80/1.51  tff(c_18, plain, (![A_11]: (k9_relat_1(A_11, k1_relat_1(A_11))=k2_relat_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.80/1.51  tff(c_231, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_18])).
% 2.80/1.51  tff(c_381, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_272, c_231])).
% 2.80/1.51  tff(c_413, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_407, c_381])).
% 2.80/1.51  tff(c_430, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_6, c_413])).
% 2.80/1.51  tff(c_22, plain, (![A_17]: (k10_relat_1(A_17, k2_relat_1(A_17))=k1_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.80/1.51  tff(c_438, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_430, c_22])).
% 2.80/1.51  tff(c_442, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_272, c_220, c_438])).
% 2.80/1.51  tff(c_317, plain, (![A_55, C_56, B_57]: (k3_xboole_0(A_55, k10_relat_1(C_56, B_57))=k10_relat_1(k7_relat_1(C_56, A_55), B_57) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.51  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.51  tff(c_603, plain, (![A_72, C_73, B_74]: (k5_xboole_0(A_72, k10_relat_1(k7_relat_1(C_73, A_72), B_74))=k4_xboole_0(A_72, k10_relat_1(C_73, B_74)) | ~v1_relat_1(C_73))), inference(superposition, [status(thm), theory('equality')], [c_317, c_12])).
% 2.80/1.51  tff(c_621, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_442, c_603])).
% 2.80/1.51  tff(c_637, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_118, c_621])).
% 2.80/1.51  tff(c_639, plain, $false, inference(negUnitSimplification, [status(thm)], [c_81, c_637])).
% 2.80/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.51  
% 2.80/1.51  Inference rules
% 2.80/1.51  ----------------------
% 2.80/1.51  #Ref     : 0
% 2.80/1.51  #Sup     : 146
% 2.80/1.51  #Fact    : 0
% 2.80/1.51  #Define  : 0
% 2.80/1.51  #Split   : 2
% 2.80/1.51  #Chain   : 0
% 2.80/1.51  #Close   : 0
% 2.80/1.51  
% 2.80/1.51  Ordering : KBO
% 2.80/1.51  
% 2.80/1.51  Simplification rules
% 2.80/1.51  ----------------------
% 2.80/1.51  #Subsume      : 7
% 2.80/1.51  #Demod        : 86
% 2.80/1.51  #Tautology    : 79
% 2.80/1.51  #SimpNegUnit  : 1
% 2.80/1.51  #BackRed      : 1
% 2.80/1.51  
% 2.80/1.51  #Partial instantiations: 0
% 2.80/1.51  #Strategies tried      : 1
% 2.80/1.51  
% 2.80/1.51  Timing (in seconds)
% 2.80/1.51  ----------------------
% 2.80/1.51  Preprocessing        : 0.32
% 2.80/1.51  Parsing              : 0.18
% 2.80/1.51  CNF conversion       : 0.02
% 2.80/1.51  Main loop            : 0.36
% 2.80/1.51  Inferencing          : 0.15
% 2.80/1.51  Reduction            : 0.11
% 2.80/1.51  Demodulation         : 0.08
% 2.80/1.51  BG Simplification    : 0.02
% 2.80/1.51  Subsumption          : 0.06
% 2.80/1.51  Abstraction          : 0.02
% 2.80/1.51  MUC search           : 0.00
% 2.80/1.51  Cooper               : 0.00
% 2.80/1.51  Total                : 0.72
% 2.80/1.51  Index Insertion      : 0.00
% 2.80/1.51  Index Deletion       : 0.00
% 2.80/1.51  Index Matching       : 0.00
% 2.80/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
