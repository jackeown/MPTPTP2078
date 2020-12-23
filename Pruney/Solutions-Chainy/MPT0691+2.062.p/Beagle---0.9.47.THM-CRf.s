%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.78s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 211 expanded)
%              Number of leaves         :   28 (  83 expanded)
%              Depth                    :   14
%              Number of atoms          :   85 ( 386 expanded)
%              Number of equality atoms :   38 ( 121 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_54,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | k4_xboole_0(A_27,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_58,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_28])).

tff(c_32,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_59])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_101,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_113,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_110])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k7_relat_1(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_168,plain,(
    ! [B_44,A_45] :
      ( k1_relat_1(k7_relat_1(B_44,A_45)) = A_45
      | ~ r1_tarski(A_45,k1_relat_1(B_44))
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_175,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_168])).

tff(c_183,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_175])).

tff(c_192,plain,(
    ! [B_46] :
      ( k1_relat_1(k7_relat_1(B_46,k1_relat_1(B_46))) = k1_relat_1(B_46)
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_8,c_168])).

tff(c_210,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_192])).

tff(c_213,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_210])).

tff(c_237,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_240,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_237])).

tff(c_244,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_240])).

tff(c_246,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_22,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_214,plain,(
    ! [A_47,C_48,B_49] :
      ( k3_xboole_0(A_47,k10_relat_1(C_48,B_49)) = k10_relat_1(k7_relat_1(C_48,A_47),B_49)
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_375,plain,(
    ! [C_54,B_55] :
      ( k10_relat_1(k7_relat_1(C_54,k10_relat_1(C_54,B_55)),B_55) = k10_relat_1(C_54,B_55)
      | ~ v1_relat_1(C_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_214])).

tff(c_443,plain,(
    ! [A_61] :
      ( k10_relat_1(k7_relat_1(A_61,k1_relat_1(A_61)),k2_relat_1(A_61)) = k10_relat_1(A_61,k2_relat_1(A_61))
      | ~ v1_relat_1(A_61)
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_375])).

tff(c_480,plain,
    ( k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_443])).

tff(c_489,plain,(
    k10_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_480])).

tff(c_230,plain,(
    ! [A_15,A_47] :
      ( k10_relat_1(k7_relat_1(A_15,A_47),k2_relat_1(A_15)) = k3_xboole_0(A_47,k1_relat_1(A_15))
      | ~ v1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_214])).

tff(c_730,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_230])).

tff(c_748,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_246,c_2,c_183,c_730])).

tff(c_786,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_748])).

tff(c_807,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_786])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_220,plain,(
    ! [A_47,C_48,B_49] :
      ( k5_xboole_0(A_47,k10_relat_1(k7_relat_1(C_48,A_47),B_49)) = k4_xboole_0(A_47,k10_relat_1(C_48,B_49))
      | ~ v1_relat_1(C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_14])).

tff(c_818,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_807,c_220])).

tff(c_833,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_113,c_818])).

tff(c_835,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_833])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:49:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.39  
% 2.78/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.39  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.78/1.39  
% 2.78/1.39  %Foreground sorts:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Background operators:
% 2.78/1.39  
% 2.78/1.39  
% 2.78/1.39  %Foreground operators:
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.78/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.78/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.78/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.78/1.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.78/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.78/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.78/1.39  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.78/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.78/1.39  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.78/1.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.78/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.78/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.78/1.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.78/1.39  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.78/1.39  
% 2.78/1.40  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.78/1.40  tff(f_70, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.78/1.40  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.78/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.78/1.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.78/1.40  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.78/1.40  tff(f_45, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.78/1.40  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 2.78/1.40  tff(f_53, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 2.78/1.40  tff(f_63, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.78/1.40  tff(c_54, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | k4_xboole_0(A_27, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.40  tff(c_28, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.40  tff(c_58, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_28])).
% 2.78/1.40  tff(c_32, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.78/1.40  tff(c_59, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.78/1.40  tff(c_71, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_59])).
% 2.78/1.40  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.78/1.40  tff(c_101, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.40  tff(c_110, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 2.78/1.40  tff(c_113, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_110])).
% 2.78/1.40  tff(c_20, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.78/1.40  tff(c_18, plain, (![A_11, B_12]: (v1_relat_1(k7_relat_1(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.78/1.40  tff(c_30, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.78/1.40  tff(c_168, plain, (![B_44, A_45]: (k1_relat_1(k7_relat_1(B_44, A_45))=A_45 | ~r1_tarski(A_45, k1_relat_1(B_44)) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.78/1.40  tff(c_175, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_168])).
% 2.78/1.40  tff(c_183, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_175])).
% 2.78/1.40  tff(c_192, plain, (![B_46]: (k1_relat_1(k7_relat_1(B_46, k1_relat_1(B_46)))=k1_relat_1(B_46) | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_8, c_168])).
% 2.78/1.40  tff(c_210, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_192])).
% 2.78/1.40  tff(c_213, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_210])).
% 2.78/1.40  tff(c_237, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_213])).
% 2.78/1.40  tff(c_240, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_237])).
% 2.78/1.40  tff(c_244, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_240])).
% 2.78/1.40  tff(c_246, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_213])).
% 2.78/1.40  tff(c_22, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.78/1.40  tff(c_214, plain, (![A_47, C_48, B_49]: (k3_xboole_0(A_47, k10_relat_1(C_48, B_49))=k10_relat_1(k7_relat_1(C_48, A_47), B_49) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.78/1.40  tff(c_375, plain, (![C_54, B_55]: (k10_relat_1(k7_relat_1(C_54, k10_relat_1(C_54, B_55)), B_55)=k10_relat_1(C_54, B_55) | ~v1_relat_1(C_54))), inference(superposition, [status(thm), theory('equality')], [c_2, c_214])).
% 2.78/1.40  tff(c_443, plain, (![A_61]: (k10_relat_1(k7_relat_1(A_61, k1_relat_1(A_61)), k2_relat_1(A_61))=k10_relat_1(A_61, k2_relat_1(A_61)) | ~v1_relat_1(A_61) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_22, c_375])).
% 2.78/1.40  tff(c_480, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_443])).
% 2.78/1.40  tff(c_489, plain, (k10_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_480])).
% 2.78/1.40  tff(c_230, plain, (![A_15, A_47]: (k10_relat_1(k7_relat_1(A_15, A_47), k2_relat_1(A_15))=k3_xboole_0(A_47, k1_relat_1(A_15)) | ~v1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(superposition, [status(thm), theory('equality')], [c_22, c_214])).
% 2.78/1.40  tff(c_730, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))=k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_489, c_230])).
% 2.78/1.40  tff(c_748, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_246, c_2, c_183, c_730])).
% 2.78/1.40  tff(c_786, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_20, c_748])).
% 2.78/1.40  tff(c_807, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_786])).
% 2.78/1.40  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.78/1.40  tff(c_220, plain, (![A_47, C_48, B_49]: (k5_xboole_0(A_47, k10_relat_1(k7_relat_1(C_48, A_47), B_49))=k4_xboole_0(A_47, k10_relat_1(C_48, B_49)) | ~v1_relat_1(C_48))), inference(superposition, [status(thm), theory('equality')], [c_214, c_14])).
% 2.78/1.40  tff(c_818, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_807, c_220])).
% 2.78/1.40  tff(c_833, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_32, c_113, c_818])).
% 2.78/1.40  tff(c_835, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_833])).
% 2.78/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.78/1.40  
% 2.78/1.40  Inference rules
% 2.78/1.40  ----------------------
% 2.78/1.40  #Ref     : 0
% 2.78/1.40  #Sup     : 197
% 2.78/1.40  #Fact    : 0
% 2.78/1.40  #Define  : 0
% 2.78/1.40  #Split   : 3
% 2.78/1.40  #Chain   : 0
% 2.78/1.40  #Close   : 0
% 2.78/1.41  
% 2.78/1.41  Ordering : KBO
% 2.78/1.41  
% 2.78/1.41  Simplification rules
% 2.78/1.41  ----------------------
% 2.78/1.41  #Subsume      : 7
% 2.78/1.41  #Demod        : 123
% 2.78/1.41  #Tautology    : 90
% 2.78/1.41  #SimpNegUnit  : 1
% 2.78/1.41  #BackRed      : 3
% 2.78/1.41  
% 2.78/1.41  #Partial instantiations: 0
% 2.78/1.41  #Strategies tried      : 1
% 2.78/1.41  
% 2.78/1.41  Timing (in seconds)
% 2.78/1.41  ----------------------
% 2.78/1.41  Preprocessing        : 0.30
% 2.78/1.41  Parsing              : 0.16
% 2.78/1.41  CNF conversion       : 0.02
% 2.78/1.41  Main loop            : 0.35
% 2.78/1.41  Inferencing          : 0.13
% 2.78/1.41  Reduction            : 0.10
% 2.78/1.41  Demodulation         : 0.07
% 2.78/1.41  BG Simplification    : 0.02
% 2.78/1.41  Subsumption          : 0.07
% 2.78/1.41  Abstraction          : 0.02
% 2.78/1.41  MUC search           : 0.00
% 2.78/1.41  Cooper               : 0.00
% 2.78/1.41  Total                : 0.68
% 2.78/1.41  Index Insertion      : 0.00
% 2.78/1.41  Index Deletion       : 0.00
% 2.78/1.41  Index Matching       : 0.00
% 2.78/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
