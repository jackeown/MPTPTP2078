%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 157 expanded)
%              Number of leaves         :   32 (  67 expanded)
%              Depth                    :   14
%              Number of atoms          :   82 ( 269 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_85,plain,(
    ! [A_44,B_45] :
      ( r1_tarski(A_44,B_45)
      | k4_xboole_0(A_44,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_89,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_85,c_42])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_99,plain,(
    ! [A_48,B_49] :
      ( k4_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_111,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_160,plain,(
    ! [A_55,B_56] : k5_xboole_0(A_55,k3_xboole_0(A_55,B_56)) = k4_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_169,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_160])).

tff(c_175,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_169])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( v1_relat_1(k7_relat_1(A_24,B_25))
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_305,plain,(
    ! [B_70,A_71] :
      ( k1_relat_1(k7_relat_1(B_70,A_71)) = A_71
      | ~ r1_tarski(A_71,k1_relat_1(B_70))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_312,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_305])).

tff(c_320,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_312])).

tff(c_332,plain,(
    ! [B_72] :
      ( k1_relat_1(k7_relat_1(B_72,k1_relat_1(B_72))) = k1_relat_1(B_72)
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_8,c_305])).

tff(c_353,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_332])).

tff(c_356,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_320,c_353])).

tff(c_409,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_412,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_409])).

tff(c_416,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_412])).

tff(c_418,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_528,plain,(
    ! [A_87,C_88,B_89] :
      ( k9_relat_1(k7_relat_1(A_87,C_88),B_89) = k9_relat_1(A_87,B_89)
      | ~ r1_tarski(B_89,C_88)
      | ~ v1_relat_1(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    ! [A_26] :
      ( k9_relat_1(A_26,k1_relat_1(A_26)) = k2_relat_1(A_26)
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_328,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_320,c_32])).

tff(c_420,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_328])).

tff(c_534,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_528,c_420])).

tff(c_551,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_534])).

tff(c_36,plain,(
    ! [A_32] :
      ( k10_relat_1(A_32,k2_relat_1(A_32)) = k1_relat_1(A_32)
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_559,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_551,c_36])).

tff(c_563,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_320,c_559])).

tff(c_383,plain,(
    ! [A_79,C_80,B_81] :
      ( k3_xboole_0(A_79,k10_relat_1(C_80,B_81)) = k10_relat_1(k7_relat_1(C_80,A_79),B_81)
      | ~ v1_relat_1(C_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_745,plain,(
    ! [A_94,C_95,B_96] :
      ( k5_xboole_0(A_94,k10_relat_1(k7_relat_1(C_95,A_94),B_96)) = k4_xboole_0(A_94,k10_relat_1(C_95,B_96))
      | ~ v1_relat_1(C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_14])).

tff(c_760,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_563,c_745])).

tff(c_775,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_175,c_760])).

tff(c_777,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_89,c_775])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:21:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.48  
% 2.61/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.48  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.61/1.48  
% 2.61/1.48  %Foreground sorts:
% 2.61/1.48  
% 2.61/1.48  
% 2.61/1.48  %Background operators:
% 2.61/1.48  
% 2.61/1.48  
% 2.61/1.48  %Foreground operators:
% 2.61/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.48  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.61/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.48  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.61/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.61/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.61/1.48  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.61/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.61/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.48  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.61/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.61/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.61/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.48  
% 2.61/1.49  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.61/1.49  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.61/1.49  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.61/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.49  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.61/1.49  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.61/1.49  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.61/1.49  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.61/1.49  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.61/1.49  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.61/1.49  tff(c_85, plain, (![A_44, B_45]: (r1_tarski(A_44, B_45) | k4_xboole_0(A_44, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.49  tff(c_42, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.49  tff(c_89, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_85, c_42])).
% 2.61/1.49  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.49  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.49  tff(c_99, plain, (![A_48, B_49]: (k4_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.49  tff(c_111, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 2.61/1.49  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.49  tff(c_160, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k3_xboole_0(A_55, B_56))=k4_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.49  tff(c_169, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_160])).
% 2.61/1.49  tff(c_175, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_111, c_169])).
% 2.61/1.49  tff(c_30, plain, (![A_24, B_25]: (v1_relat_1(k7_relat_1(A_24, B_25)) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.61/1.49  tff(c_44, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.61/1.49  tff(c_305, plain, (![B_70, A_71]: (k1_relat_1(k7_relat_1(B_70, A_71))=A_71 | ~r1_tarski(A_71, k1_relat_1(B_70)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.61/1.49  tff(c_312, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_305])).
% 2.61/1.49  tff(c_320, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_312])).
% 2.61/1.49  tff(c_332, plain, (![B_72]: (k1_relat_1(k7_relat_1(B_72, k1_relat_1(B_72)))=k1_relat_1(B_72) | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_8, c_305])).
% 2.61/1.49  tff(c_353, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_332])).
% 2.61/1.49  tff(c_356, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_320, c_353])).
% 2.61/1.49  tff(c_409, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_356])).
% 2.61/1.49  tff(c_412, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_409])).
% 2.61/1.49  tff(c_416, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_412])).
% 2.61/1.49  tff(c_418, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_356])).
% 2.61/1.49  tff(c_528, plain, (![A_87, C_88, B_89]: (k9_relat_1(k7_relat_1(A_87, C_88), B_89)=k9_relat_1(A_87, B_89) | ~r1_tarski(B_89, C_88) | ~v1_relat_1(A_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.61/1.49  tff(c_32, plain, (![A_26]: (k9_relat_1(A_26, k1_relat_1(A_26))=k2_relat_1(A_26) | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.61/1.49  tff(c_328, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_320, c_32])).
% 2.61/1.49  tff(c_420, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_328])).
% 2.61/1.49  tff(c_534, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_528, c_420])).
% 2.61/1.49  tff(c_551, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_534])).
% 2.61/1.49  tff(c_36, plain, (![A_32]: (k10_relat_1(A_32, k2_relat_1(A_32))=k1_relat_1(A_32) | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.61/1.49  tff(c_559, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_551, c_36])).
% 2.61/1.49  tff(c_563, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_418, c_320, c_559])).
% 2.61/1.49  tff(c_383, plain, (![A_79, C_80, B_81]: (k3_xboole_0(A_79, k10_relat_1(C_80, B_81))=k10_relat_1(k7_relat_1(C_80, A_79), B_81) | ~v1_relat_1(C_80))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.61/1.49  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.49  tff(c_745, plain, (![A_94, C_95, B_96]: (k5_xboole_0(A_94, k10_relat_1(k7_relat_1(C_95, A_94), B_96))=k4_xboole_0(A_94, k10_relat_1(C_95, B_96)) | ~v1_relat_1(C_95))), inference(superposition, [status(thm), theory('equality')], [c_383, c_14])).
% 2.61/1.49  tff(c_760, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_563, c_745])).
% 2.61/1.49  tff(c_775, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_175, c_760])).
% 2.61/1.49  tff(c_777, plain, $false, inference(negUnitSimplification, [status(thm)], [c_89, c_775])).
% 2.61/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.61/1.49  
% 2.61/1.49  Inference rules
% 2.61/1.49  ----------------------
% 2.61/1.49  #Ref     : 0
% 2.61/1.49  #Sup     : 179
% 2.61/1.49  #Fact    : 0
% 2.61/1.49  #Define  : 0
% 2.61/1.49  #Split   : 2
% 2.61/1.49  #Chain   : 0
% 2.61/1.49  #Close   : 0
% 2.61/1.49  
% 2.61/1.49  Ordering : KBO
% 2.61/1.49  
% 2.61/1.49  Simplification rules
% 2.61/1.49  ----------------------
% 2.61/1.49  #Subsume      : 4
% 2.61/1.49  #Demod        : 105
% 2.61/1.49  #Tautology    : 110
% 2.61/1.49  #SimpNegUnit  : 1
% 2.61/1.49  #BackRed      : 1
% 2.61/1.49  
% 2.61/1.49  #Partial instantiations: 0
% 2.61/1.49  #Strategies tried      : 1
% 2.61/1.49  
% 2.61/1.49  Timing (in seconds)
% 2.61/1.49  ----------------------
% 2.61/1.50  Preprocessing        : 0.33
% 2.61/1.50  Parsing              : 0.18
% 2.61/1.50  CNF conversion       : 0.02
% 2.61/1.50  Main loop            : 0.31
% 2.61/1.50  Inferencing          : 0.11
% 2.61/1.50  Reduction            : 0.10
% 2.61/1.50  Demodulation         : 0.07
% 2.61/1.50  BG Simplification    : 0.02
% 2.61/1.50  Subsumption          : 0.05
% 2.61/1.50  Abstraction          : 0.02
% 2.61/1.50  MUC search           : 0.00
% 2.61/1.50  Cooper               : 0.00
% 2.61/1.50  Total                : 0.67
% 2.61/1.50  Index Insertion      : 0.00
% 2.61/1.50  Index Deletion       : 0.00
% 2.61/1.50  Index Matching       : 0.00
% 2.61/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
