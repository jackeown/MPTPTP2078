%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:37 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   49 (  59 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   54 (  70 expanded)
%              Number of equality atoms :   27 (  30 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_41,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_19] : v1_relat_1(k6_relat_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_12,plain,(
    ! [A_13] : k1_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_26] :
      ( k7_relat_1(A_26,k1_relat_1(A_26)) = A_26
      | ~ v1_relat_1(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_57,plain,(
    ! [A_13] :
      ( k7_relat_1(k6_relat_1(A_13),A_13) = k6_relat_1(A_13)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_48])).

tff(c_61,plain,(
    ! [A_13] : k7_relat_1(k6_relat_1(A_13),A_13) = k6_relat_1(A_13) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_57])).

tff(c_141,plain,(
    ! [C_41,A_42,B_43] :
      ( k7_relat_1(k7_relat_1(C_41,A_42),B_43) = k7_relat_1(C_41,k3_xboole_0(A_42,B_43))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_160,plain,(
    ! [A_13,B_43] :
      ( k7_relat_1(k6_relat_1(A_13),k3_xboole_0(A_13,B_43)) = k7_relat_1(k6_relat_1(A_13),B_43)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_141])).

tff(c_211,plain,(
    ! [A_46,B_47] : k7_relat_1(k6_relat_1(A_46),k3_xboole_0(A_46,B_47)) = k7_relat_1(k6_relat_1(A_46),B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_160])).

tff(c_14,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    ! [B_37,A_38] :
      ( k5_relat_1(B_37,k6_relat_1(A_38)) = B_37
      | ~ r1_tarski(k2_relat_1(B_37),A_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_115,plain,(
    ! [A_13,A_38] :
      ( k5_relat_1(k6_relat_1(A_13),k6_relat_1(A_38)) = k6_relat_1(A_13)
      | ~ r1_tarski(A_13,A_38)
      | ~ v1_relat_1(k6_relat_1(A_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_112])).

tff(c_118,plain,(
    ! [A_39,A_40] :
      ( k5_relat_1(k6_relat_1(A_39),k6_relat_1(A_40)) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k5_relat_1(k6_relat_1(A_16),B_17) = k7_relat_1(B_17,A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_124,plain,(
    ! [A_40,A_39] :
      ( k7_relat_1(k6_relat_1(A_40),A_39) = k6_relat_1(A_39)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_18])).

tff(c_137,plain,(
    ! [A_40,A_39] :
      ( k7_relat_1(k6_relat_1(A_40),A_39) = k6_relat_1(A_39)
      | ~ r1_tarski(A_39,A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_124])).

tff(c_217,plain,(
    ! [A_46,B_47] :
      ( k7_relat_1(k6_relat_1(A_46),B_47) = k6_relat_1(k3_xboole_0(A_46,B_47))
      | ~ r1_tarski(k3_xboole_0(A_46,B_47),A_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_137])).

tff(c_230,plain,(
    ! [A_46,B_47] : k7_relat_1(k6_relat_1(A_46),B_47) = k6_relat_1(k3_xboole_0(A_46,B_47)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_217])).

tff(c_89,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_26,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_95,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_26])).

tff(c_101,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_95])).

tff(c_240,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  
% 1.88/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.19  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.88/1.19  
% 1.88/1.19  %Foreground sorts:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Background operators:
% 1.88/1.19  
% 1.88/1.19  
% 1.88/1.19  %Foreground operators:
% 1.88/1.19  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.88/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.88/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.88/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.88/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.88/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.88/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.88/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.88/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.88/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.88/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.88/1.19  
% 1.88/1.20  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.88/1.20  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.88/1.20  tff(f_41, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.88/1.20  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 1.88/1.20  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.88/1.20  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 1.88/1.20  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 1.88/1.20  tff(f_62, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 1.88/1.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.88/1.20  tff(c_22, plain, (![A_19]: (v1_relat_1(k6_relat_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.88/1.20  tff(c_12, plain, (![A_13]: (k1_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.20  tff(c_48, plain, (![A_26]: (k7_relat_1(A_26, k1_relat_1(A_26))=A_26 | ~v1_relat_1(A_26))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.88/1.20  tff(c_57, plain, (![A_13]: (k7_relat_1(k6_relat_1(A_13), A_13)=k6_relat_1(A_13) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_48])).
% 1.88/1.20  tff(c_61, plain, (![A_13]: (k7_relat_1(k6_relat_1(A_13), A_13)=k6_relat_1(A_13))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_57])).
% 1.88/1.20  tff(c_141, plain, (![C_41, A_42, B_43]: (k7_relat_1(k7_relat_1(C_41, A_42), B_43)=k7_relat_1(C_41, k3_xboole_0(A_42, B_43)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.88/1.20  tff(c_160, plain, (![A_13, B_43]: (k7_relat_1(k6_relat_1(A_13), k3_xboole_0(A_13, B_43))=k7_relat_1(k6_relat_1(A_13), B_43) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_61, c_141])).
% 1.88/1.20  tff(c_211, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), k3_xboole_0(A_46, B_47))=k7_relat_1(k6_relat_1(A_46), B_47))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_160])).
% 1.88/1.20  tff(c_14, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.20  tff(c_112, plain, (![B_37, A_38]: (k5_relat_1(B_37, k6_relat_1(A_38))=B_37 | ~r1_tarski(k2_relat_1(B_37), A_38) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.88/1.20  tff(c_115, plain, (![A_13, A_38]: (k5_relat_1(k6_relat_1(A_13), k6_relat_1(A_38))=k6_relat_1(A_13) | ~r1_tarski(A_13, A_38) | ~v1_relat_1(k6_relat_1(A_13)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_112])).
% 1.88/1.20  tff(c_118, plain, (![A_39, A_40]: (k5_relat_1(k6_relat_1(A_39), k6_relat_1(A_40))=k6_relat_1(A_39) | ~r1_tarski(A_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_115])).
% 1.88/1.20  tff(c_18, plain, (![A_16, B_17]: (k5_relat_1(k6_relat_1(A_16), B_17)=k7_relat_1(B_17, A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.20  tff(c_124, plain, (![A_40, A_39]: (k7_relat_1(k6_relat_1(A_40), A_39)=k6_relat_1(A_39) | ~v1_relat_1(k6_relat_1(A_40)) | ~r1_tarski(A_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_118, c_18])).
% 1.88/1.20  tff(c_137, plain, (![A_40, A_39]: (k7_relat_1(k6_relat_1(A_40), A_39)=k6_relat_1(A_39) | ~r1_tarski(A_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_124])).
% 1.88/1.20  tff(c_217, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), B_47)=k6_relat_1(k3_xboole_0(A_46, B_47)) | ~r1_tarski(k3_xboole_0(A_46, B_47), A_46))), inference(superposition, [status(thm), theory('equality')], [c_211, c_137])).
% 1.88/1.20  tff(c_230, plain, (![A_46, B_47]: (k7_relat_1(k6_relat_1(A_46), B_47)=k6_relat_1(k3_xboole_0(A_46, B_47)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_217])).
% 1.88/1.20  tff(c_89, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.20  tff(c_26, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.88/1.20  tff(c_95, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_89, c_26])).
% 1.88/1.20  tff(c_101, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_95])).
% 1.88/1.20  tff(c_240, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_230, c_101])).
% 1.88/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  Inference rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Ref     : 0
% 1.88/1.20  #Sup     : 45
% 1.88/1.20  #Fact    : 0
% 1.88/1.20  #Define  : 0
% 1.88/1.20  #Split   : 1
% 1.88/1.20  #Chain   : 0
% 1.88/1.20  #Close   : 0
% 1.88/1.20  
% 1.88/1.20  Ordering : KBO
% 1.88/1.20  
% 1.88/1.20  Simplification rules
% 1.88/1.20  ----------------------
% 1.88/1.20  #Subsume      : 2
% 1.88/1.20  #Demod        : 19
% 1.88/1.20  #Tautology    : 28
% 1.88/1.20  #SimpNegUnit  : 0
% 1.88/1.20  #BackRed      : 3
% 1.88/1.20  
% 1.88/1.20  #Partial instantiations: 0
% 1.88/1.20  #Strategies tried      : 1
% 1.88/1.20  
% 1.88/1.20  Timing (in seconds)
% 1.88/1.20  ----------------------
% 1.88/1.21  Preprocessing        : 0.29
% 1.88/1.21  Parsing              : 0.16
% 1.88/1.21  CNF conversion       : 0.02
% 1.88/1.21  Main loop            : 0.15
% 1.88/1.21  Inferencing          : 0.06
% 1.88/1.21  Reduction            : 0.05
% 1.88/1.21  Demodulation         : 0.04
% 1.88/1.21  BG Simplification    : 0.01
% 1.88/1.21  Subsumption          : 0.02
% 1.88/1.21  Abstraction          : 0.01
% 1.88/1.21  MUC search           : 0.00
% 1.88/1.21  Cooper               : 0.00
% 1.88/1.21  Total                : 0.46
% 1.88/1.21  Index Insertion      : 0.00
% 1.88/1.21  Index Deletion       : 0.00
% 1.88/1.21  Index Matching       : 0.00
% 1.88/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
