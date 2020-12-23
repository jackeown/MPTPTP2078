%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.09s
% Verified   : 
% Statistics : Number of formulae       :   46 (  65 expanded)
%              Number of leaves         :   20 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 103 expanded)
%              Number of equality atoms :   27 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_65,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_85,plain,(
    ! [B_27,A_28] :
      ( r1_tarski(k7_relat_1(B_27,A_28),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_88,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(k7_relat_1(B_27,A_28),B_27) = k7_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(resolution,[status(thm)],[c_85,c_10])).

tff(c_90,plain,(
    ! [B_27,A_28] :
      ( k3_xboole_0(B_27,k7_relat_1(B_27,A_28)) = k7_relat_1(B_27,A_28)
      | ~ v1_relat_1(B_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_88])).

tff(c_101,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(k1_relat_1(B_31),A_32) = k1_relat_1(k7_relat_1(B_31,A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_125,plain,(
    ! [B_2,B_31] :
      ( k3_xboole_0(B_2,k1_relat_1(B_31)) = k1_relat_1(k7_relat_1(B_31,B_2))
      | ~ v1_relat_1(B_31) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_150,plain,(
    ! [B_34,A_35] :
      ( k7_relat_1(B_34,A_35) = B_34
      | ~ r1_tarski(k1_relat_1(B_34),A_35)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_158,plain,(
    ! [B_34] :
      ( k7_relat_1(B_34,k1_relat_1(B_34)) = B_34
      | ~ v1_relat_1(B_34) ) ),
    inference(resolution,[status(thm)],[c_8,c_150])).

tff(c_179,plain,(
    ! [C_37,A_38,B_39] :
      ( k3_xboole_0(k7_relat_1(C_37,A_38),k7_relat_1(C_37,B_39)) = k7_relat_1(C_37,k3_xboole_0(A_38,B_39))
      | ~ v1_relat_1(C_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_286,plain,(
    ! [C_46,B_47,A_48] :
      ( k3_xboole_0(k7_relat_1(C_46,B_47),k7_relat_1(C_46,A_48)) = k7_relat_1(C_46,k3_xboole_0(A_48,B_47))
      | ~ v1_relat_1(C_46) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_2])).

tff(c_744,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,k3_xboole_0(A_62,k1_relat_1(B_61))) = k3_xboole_0(B_61,k7_relat_1(B_61,A_62))
      | ~ v1_relat_1(B_61)
      | ~ v1_relat_1(B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_286])).

tff(c_1078,plain,(
    ! [B_69,B_70] :
      ( k7_relat_1(B_69,k1_relat_1(k7_relat_1(B_69,B_70))) = k3_xboole_0(B_69,k7_relat_1(B_69,B_70))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_744])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_217,plain,(
    ! [B_40,B_41] :
      ( k3_xboole_0(B_40,k1_relat_1(B_41)) = k1_relat_1(k7_relat_1(B_41,B_40))
      | ~ v1_relat_1(B_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_101])).

tff(c_18,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_330,plain,(
    ! [B_50,B_49] :
      ( k1_relat_1(k7_relat_1(B_50,k1_relat_1(B_49))) = k1_relat_1(k7_relat_1(B_49,k1_relat_1(B_50)))
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_18])).

tff(c_22,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_387,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_330,c_22])).

tff(c_426,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_26,c_387])).

tff(c_1100,plain,
    ( k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1078,c_426])).

tff(c_1160,plain,(
    k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_26,c_1100])).

tff(c_1164,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_1160])).

tff(c_1168,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:49 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  
% 3.09/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.48  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.09/1.48  
% 3.09/1.48  %Foreground sorts:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Background operators:
% 3.09/1.48  
% 3.09/1.48  
% 3.09/1.48  %Foreground operators:
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.48  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.09/1.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.48  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.48  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.09/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.48  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.09/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.09/1.48  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.09/1.48  
% 3.09/1.49  tff(f_65, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 3.09/1.49  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.09/1.49  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 3.09/1.49  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.09/1.49  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.09/1.49  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.09/1.49  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.09/1.49  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_relat_1)).
% 3.09/1.49  tff(c_26, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.49  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.09/1.49  tff(c_85, plain, (![B_27, A_28]: (r1_tarski(k7_relat_1(B_27, A_28), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.09/1.49  tff(c_10, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.09/1.49  tff(c_88, plain, (![B_27, A_28]: (k3_xboole_0(k7_relat_1(B_27, A_28), B_27)=k7_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(resolution, [status(thm)], [c_85, c_10])).
% 3.09/1.49  tff(c_90, plain, (![B_27, A_28]: (k3_xboole_0(B_27, k7_relat_1(B_27, A_28))=k7_relat_1(B_27, A_28) | ~v1_relat_1(B_27))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_88])).
% 3.09/1.49  tff(c_101, plain, (![B_31, A_32]: (k3_xboole_0(k1_relat_1(B_31), A_32)=k1_relat_1(k7_relat_1(B_31, A_32)) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.49  tff(c_125, plain, (![B_2, B_31]: (k3_xboole_0(B_2, k1_relat_1(B_31))=k1_relat_1(k7_relat_1(B_31, B_2)) | ~v1_relat_1(B_31))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 3.09/1.49  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.09/1.49  tff(c_150, plain, (![B_34, A_35]: (k7_relat_1(B_34, A_35)=B_34 | ~r1_tarski(k1_relat_1(B_34), A_35) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.09/1.49  tff(c_158, plain, (![B_34]: (k7_relat_1(B_34, k1_relat_1(B_34))=B_34 | ~v1_relat_1(B_34))), inference(resolution, [status(thm)], [c_8, c_150])).
% 3.09/1.49  tff(c_179, plain, (![C_37, A_38, B_39]: (k3_xboole_0(k7_relat_1(C_37, A_38), k7_relat_1(C_37, B_39))=k7_relat_1(C_37, k3_xboole_0(A_38, B_39)) | ~v1_relat_1(C_37))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.09/1.49  tff(c_286, plain, (![C_46, B_47, A_48]: (k3_xboole_0(k7_relat_1(C_46, B_47), k7_relat_1(C_46, A_48))=k7_relat_1(C_46, k3_xboole_0(A_48, B_47)) | ~v1_relat_1(C_46))), inference(superposition, [status(thm), theory('equality')], [c_179, c_2])).
% 3.09/1.49  tff(c_744, plain, (![B_61, A_62]: (k7_relat_1(B_61, k3_xboole_0(A_62, k1_relat_1(B_61)))=k3_xboole_0(B_61, k7_relat_1(B_61, A_62)) | ~v1_relat_1(B_61) | ~v1_relat_1(B_61))), inference(superposition, [status(thm), theory('equality')], [c_158, c_286])).
% 3.09/1.49  tff(c_1078, plain, (![B_69, B_70]: (k7_relat_1(B_69, k1_relat_1(k7_relat_1(B_69, B_70)))=k3_xboole_0(B_69, k7_relat_1(B_69, B_70)) | ~v1_relat_1(B_69) | ~v1_relat_1(B_69) | ~v1_relat_1(B_69))), inference(superposition, [status(thm), theory('equality')], [c_125, c_744])).
% 3.09/1.49  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.49  tff(c_217, plain, (![B_40, B_41]: (k3_xboole_0(B_40, k1_relat_1(B_41))=k1_relat_1(k7_relat_1(B_41, B_40)) | ~v1_relat_1(B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_101])).
% 3.09/1.49  tff(c_18, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.09/1.49  tff(c_330, plain, (![B_50, B_49]: (k1_relat_1(k7_relat_1(B_50, k1_relat_1(B_49)))=k1_relat_1(k7_relat_1(B_49, k1_relat_1(B_50))) | ~v1_relat_1(B_50) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_217, c_18])).
% 3.09/1.49  tff(c_22, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.09/1.49  tff(c_387, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_330, c_22])).
% 3.09/1.49  tff(c_426, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_26, c_387])).
% 3.09/1.49  tff(c_1100, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1078, c_426])).
% 3.09/1.49  tff(c_1160, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_26, c_1100])).
% 3.09/1.49  tff(c_1164, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_90, c_1160])).
% 3.09/1.49  tff(c_1168, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_1164])).
% 3.09/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.49  
% 3.09/1.49  Inference rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Ref     : 0
% 3.09/1.49  #Sup     : 317
% 3.09/1.49  #Fact    : 0
% 3.09/1.49  #Define  : 0
% 3.09/1.49  #Split   : 0
% 3.09/1.49  #Chain   : 0
% 3.09/1.49  #Close   : 0
% 3.09/1.49  
% 3.09/1.49  Ordering : KBO
% 3.09/1.49  
% 3.09/1.49  Simplification rules
% 3.09/1.49  ----------------------
% 3.09/1.49  #Subsume      : 61
% 3.09/1.49  #Demod        : 35
% 3.09/1.49  #Tautology    : 78
% 3.09/1.49  #SimpNegUnit  : 0
% 3.09/1.49  #BackRed      : 0
% 3.09/1.49  
% 3.09/1.49  #Partial instantiations: 0
% 3.09/1.49  #Strategies tried      : 1
% 3.09/1.49  
% 3.09/1.49  Timing (in seconds)
% 3.09/1.49  ----------------------
% 3.09/1.49  Preprocessing        : 0.30
% 3.09/1.49  Parsing              : 0.17
% 3.09/1.49  CNF conversion       : 0.02
% 3.09/1.49  Main loop            : 0.43
% 3.09/1.49  Inferencing          : 0.17
% 3.09/1.49  Reduction            : 0.12
% 3.09/1.49  Demodulation         : 0.10
% 3.09/1.49  BG Simplification    : 0.03
% 3.09/1.49  Subsumption          : 0.08
% 3.09/1.49  Abstraction          : 0.03
% 3.09/1.50  MUC search           : 0.00
% 3.09/1.50  Cooper               : 0.00
% 3.09/1.50  Total                : 0.76
% 3.09/1.50  Index Insertion      : 0.00
% 3.09/1.50  Index Deletion       : 0.00
% 3.09/1.50  Index Matching       : 0.00
% 3.09/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
