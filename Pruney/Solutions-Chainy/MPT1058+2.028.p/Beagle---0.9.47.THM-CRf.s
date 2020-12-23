%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   50 (  58 expanded)
%              Number of leaves         :   29 (  34 expanded)
%              Depth                    :   11
%              Number of atoms          :   49 (  66 expanded)
%              Number of equality atoms :   25 (  33 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_79,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_40,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_46,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_24,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_32,plain,(
    ! [A_26] : v1_relat_1(k6_relat_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_222,plain,(
    ! [B_58,A_59] : k5_relat_1(k6_relat_1(B_58),k6_relat_1(A_59)) = k6_relat_1(k3_xboole_0(A_59,B_58)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_28,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_228,plain,(
    ! [A_59,B_58] :
      ( k7_relat_1(k6_relat_1(A_59),B_58) = k6_relat_1(k3_xboole_0(A_59,B_58))
      | ~ v1_relat_1(k6_relat_1(A_59)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_28])).

tff(c_238,plain,(
    ! [A_59,B_58] : k7_relat_1(k6_relat_1(A_59),B_58) = k6_relat_1(k3_xboole_0(A_59,B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_228])).

tff(c_327,plain,(
    ! [B_74,A_75] :
      ( k7_relat_1(B_74,A_75) = B_74
      | ~ r1_tarski(k1_relat_1(B_74),A_75)
      | ~ v1_relat_1(B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_338,plain,(
    ! [A_21,A_75] :
      ( k7_relat_1(k6_relat_1(A_21),A_75) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_75)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_327])).

tff(c_456,plain,(
    ! [A_82,A_83] :
      ( k6_relat_1(k3_xboole_0(A_82,A_83)) = k6_relat_1(A_82)
      | ~ r1_tarski(A_82,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_238,c_338])).

tff(c_474,plain,(
    ! [A_82,A_83] :
      ( k3_xboole_0(A_82,A_83) = k1_relat_1(k6_relat_1(A_82))
      | ~ r1_tarski(A_82,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_24])).

tff(c_567,plain,(
    ! [A_88,A_89] :
      ( k3_xboole_0(A_88,A_89) = A_88
      | ~ r1_tarski(A_88,A_89) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_474])).

tff(c_589,plain,(
    k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_567])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_681,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_2])).

tff(c_36,plain,(
    ! [A_27,C_29,B_28] :
      ( k3_xboole_0(A_27,k10_relat_1(C_29,B_28)) = k10_relat_1(k7_relat_1(C_29,A_27),B_28)
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_704,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_681,c_36])).

tff(c_711,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_704])).

tff(c_713,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:41:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.50/1.35  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.35  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.50/1.35  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.50/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.35  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.50/1.35  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.50/1.35  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.50/1.35  
% 2.68/1.36  tff(f_89, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 2.68/1.36  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.68/1.36  tff(f_73, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.68/1.36  tff(f_79, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 2.68/1.36  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.68/1.36  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.68/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.68/1.36  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.68/1.36  tff(c_40, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.68/1.36  tff(c_46, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.68/1.36  tff(c_42, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.68/1.36  tff(c_24, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.68/1.36  tff(c_32, plain, (![A_26]: (v1_relat_1(k6_relat_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.68/1.36  tff(c_222, plain, (![B_58, A_59]: (k5_relat_1(k6_relat_1(B_58), k6_relat_1(A_59))=k6_relat_1(k3_xboole_0(A_59, B_58)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.68/1.36  tff(c_28, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.68/1.36  tff(c_228, plain, (![A_59, B_58]: (k7_relat_1(k6_relat_1(A_59), B_58)=k6_relat_1(k3_xboole_0(A_59, B_58)) | ~v1_relat_1(k6_relat_1(A_59)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_28])).
% 2.68/1.36  tff(c_238, plain, (![A_59, B_58]: (k7_relat_1(k6_relat_1(A_59), B_58)=k6_relat_1(k3_xboole_0(A_59, B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_228])).
% 2.68/1.36  tff(c_327, plain, (![B_74, A_75]: (k7_relat_1(B_74, A_75)=B_74 | ~r1_tarski(k1_relat_1(B_74), A_75) | ~v1_relat_1(B_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.68/1.36  tff(c_338, plain, (![A_21, A_75]: (k7_relat_1(k6_relat_1(A_21), A_75)=k6_relat_1(A_21) | ~r1_tarski(A_21, A_75) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_327])).
% 2.68/1.36  tff(c_456, plain, (![A_82, A_83]: (k6_relat_1(k3_xboole_0(A_82, A_83))=k6_relat_1(A_82) | ~r1_tarski(A_82, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_238, c_338])).
% 2.68/1.36  tff(c_474, plain, (![A_82, A_83]: (k3_xboole_0(A_82, A_83)=k1_relat_1(k6_relat_1(A_82)) | ~r1_tarski(A_82, A_83))), inference(superposition, [status(thm), theory('equality')], [c_456, c_24])).
% 2.68/1.36  tff(c_567, plain, (![A_88, A_89]: (k3_xboole_0(A_88, A_89)=A_88 | ~r1_tarski(A_88, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_474])).
% 2.68/1.36  tff(c_589, plain, (k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_567])).
% 2.68/1.36  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.68/1.36  tff(c_681, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_589, c_2])).
% 2.68/1.36  tff(c_36, plain, (![A_27, C_29, B_28]: (k3_xboole_0(A_27, k10_relat_1(C_29, B_28))=k10_relat_1(k7_relat_1(C_29, A_27), B_28) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.68/1.36  tff(c_704, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_681, c_36])).
% 2.68/1.36  tff(c_711, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_704])).
% 2.68/1.36  tff(c_713, plain, $false, inference(negUnitSimplification, [status(thm)], [c_40, c_711])).
% 2.68/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.68/1.36  
% 2.68/1.36  Inference rules
% 2.68/1.36  ----------------------
% 2.68/1.36  #Ref     : 0
% 2.68/1.37  #Sup     : 160
% 2.68/1.37  #Fact    : 0
% 2.68/1.37  #Define  : 0
% 2.68/1.37  #Split   : 1
% 2.68/1.37  #Chain   : 0
% 2.68/1.37  #Close   : 0
% 2.68/1.37  
% 2.68/1.37  Ordering : KBO
% 2.68/1.37  
% 2.68/1.37  Simplification rules
% 2.68/1.37  ----------------------
% 2.68/1.37  #Subsume      : 8
% 2.68/1.37  #Demod        : 69
% 2.68/1.37  #Tautology    : 83
% 2.68/1.37  #SimpNegUnit  : 1
% 2.68/1.37  #BackRed      : 0
% 2.68/1.37  
% 2.68/1.37  #Partial instantiations: 0
% 2.68/1.37  #Strategies tried      : 1
% 2.68/1.37  
% 2.68/1.37  Timing (in seconds)
% 2.68/1.37  ----------------------
% 2.68/1.37  Preprocessing        : 0.31
% 2.68/1.37  Parsing              : 0.17
% 2.68/1.37  CNF conversion       : 0.02
% 2.68/1.37  Main loop            : 0.29
% 2.68/1.37  Inferencing          : 0.10
% 2.68/1.37  Reduction            : 0.10
% 2.68/1.37  Demodulation         : 0.08
% 2.68/1.37  BG Simplification    : 0.02
% 2.68/1.37  Subsumption          : 0.05
% 2.68/1.37  Abstraction          : 0.02
% 2.68/1.37  MUC search           : 0.00
% 2.68/1.37  Cooper               : 0.00
% 2.68/1.37  Total                : 0.63
% 2.68/1.37  Index Insertion      : 0.00
% 2.68/1.37  Index Deletion       : 0.00
% 2.68/1.37  Index Matching       : 0.00
% 2.68/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
