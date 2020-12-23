%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:00 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   44 (  52 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   58 (  75 expanded)
%              Number of equality atoms :   22 (  28 expanded)
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

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [C_34,B_35,A_36] :
      ( k7_relat_1(k7_relat_1(C_34,B_35),A_36) = k7_relat_1(C_34,A_36)
      | ~ r1_tarski(A_36,B_35)
      | ~ v1_relat_1(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_368,plain,(
    ! [C_41,B_42] :
      ( k7_relat_1(C_41,k1_relat_1(k7_relat_1(C_41,B_42))) = k7_relat_1(C_41,B_42)
      | ~ v1_relat_1(k7_relat_1(C_41,B_42))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_41,B_42)),B_42)
      | ~ v1_relat_1(C_41) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_14])).

tff(c_384,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,k1_relat_1(k7_relat_1(B_43,A_44))) = k7_relat_1(B_43,A_44)
      | ~ v1_relat_1(k7_relat_1(B_43,A_44))
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_10,c_368])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [B_30,A_31] :
      ( k3_xboole_0(k1_relat_1(B_30),A_31) = k1_relat_1(k7_relat_1(B_30,A_31))
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_67,plain,(
    ! [A_21,B_22] : k1_setfam_1(k2_tarski(A_21,B_22)) = k3_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [B_23,A_24] : k1_setfam_1(k2_tarski(B_23,A_24)) = k3_xboole_0(A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_67])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [B_23,A_24] : k3_xboole_0(B_23,A_24) = k3_xboole_0(A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_4])).

tff(c_167,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,k1_relat_1(B_33)) = k1_relat_1(k7_relat_1(B_33,A_32))
      | ~ v1_relat_1(B_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_88])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(k1_relat_1(B_13),A_12) = k1_relat_1(k7_relat_1(B_13,A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_231,plain,(
    ! [B_38,B_37] :
      ( k1_relat_1(k7_relat_1(B_38,k1_relat_1(B_37))) = k1_relat_1(k7_relat_1(B_37,k1_relat_1(B_38)))
      | ~ v1_relat_1(B_38)
      | ~ v1_relat_1(B_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_12])).

tff(c_16,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_288,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_16])).

tff(c_335,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_288])).

tff(c_396,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_335])).

tff(c_436,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_396])).

tff(c_442,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_436])).

tff(c_446,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n012.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.32  
% 2.36/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.33  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.36/1.33  
% 2.36/1.33  %Foreground sorts:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Background operators:
% 2.36/1.33  
% 2.36/1.33  
% 2.36/1.33  %Foreground operators:
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.36/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.36/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.36/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.33  
% 2.36/1.34  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 2.36/1.34  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.36/1.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.36/1.34  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.36/1.34  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 2.36/1.34  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.36/1.34  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.36/1.34  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.36/1.34  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.34  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.34  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.36/1.34  tff(c_198, plain, (![C_34, B_35, A_36]: (k7_relat_1(k7_relat_1(C_34, B_35), A_36)=k7_relat_1(C_34, A_36) | ~r1_tarski(A_36, B_35) | ~v1_relat_1(C_34))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.36/1.34  tff(c_14, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.36/1.34  tff(c_368, plain, (![C_41, B_42]: (k7_relat_1(C_41, k1_relat_1(k7_relat_1(C_41, B_42)))=k7_relat_1(C_41, B_42) | ~v1_relat_1(k7_relat_1(C_41, B_42)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_41, B_42)), B_42) | ~v1_relat_1(C_41))), inference(superposition, [status(thm), theory('equality')], [c_198, c_14])).
% 2.36/1.34  tff(c_384, plain, (![B_43, A_44]: (k7_relat_1(B_43, k1_relat_1(k7_relat_1(B_43, A_44)))=k7_relat_1(B_43, A_44) | ~v1_relat_1(k7_relat_1(B_43, A_44)) | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_10, c_368])).
% 2.36/1.34  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.34  tff(c_144, plain, (![B_30, A_31]: (k3_xboole_0(k1_relat_1(B_30), A_31)=k1_relat_1(k7_relat_1(B_30, A_31)) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.34  tff(c_67, plain, (![A_21, B_22]: (k1_setfam_1(k2_tarski(A_21, B_22))=k3_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.34  tff(c_82, plain, (![B_23, A_24]: (k1_setfam_1(k2_tarski(B_23, A_24))=k3_xboole_0(A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_2, c_67])).
% 2.36/1.34  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.34  tff(c_88, plain, (![B_23, A_24]: (k3_xboole_0(B_23, A_24)=k3_xboole_0(A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_82, c_4])).
% 2.36/1.34  tff(c_167, plain, (![A_32, B_33]: (k3_xboole_0(A_32, k1_relat_1(B_33))=k1_relat_1(k7_relat_1(B_33, A_32)) | ~v1_relat_1(B_33))), inference(superposition, [status(thm), theory('equality')], [c_144, c_88])).
% 2.36/1.34  tff(c_12, plain, (![B_13, A_12]: (k3_xboole_0(k1_relat_1(B_13), A_12)=k1_relat_1(k7_relat_1(B_13, A_12)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.36/1.34  tff(c_231, plain, (![B_38, B_37]: (k1_relat_1(k7_relat_1(B_38, k1_relat_1(B_37)))=k1_relat_1(k7_relat_1(B_37, k1_relat_1(B_38))) | ~v1_relat_1(B_38) | ~v1_relat_1(B_37))), inference(superposition, [status(thm), theory('equality')], [c_167, c_12])).
% 2.36/1.34  tff(c_16, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.36/1.34  tff(c_288, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_231, c_16])).
% 2.36/1.34  tff(c_335, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_288])).
% 2.36/1.34  tff(c_396, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_384, c_335])).
% 2.36/1.34  tff(c_436, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_396])).
% 2.36/1.34  tff(c_442, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_436])).
% 2.36/1.34  tff(c_446, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_442])).
% 2.36/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.34  
% 2.36/1.34  Inference rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Ref     : 0
% 2.36/1.34  #Sup     : 115
% 2.36/1.34  #Fact    : 0
% 2.36/1.34  #Define  : 0
% 2.36/1.34  #Split   : 0
% 2.36/1.34  #Chain   : 0
% 2.36/1.34  #Close   : 0
% 2.36/1.34  
% 2.36/1.34  Ordering : KBO
% 2.36/1.34  
% 2.36/1.34  Simplification rules
% 2.36/1.34  ----------------------
% 2.36/1.34  #Subsume      : 18
% 2.36/1.34  #Demod        : 9
% 2.36/1.34  #Tautology    : 46
% 2.36/1.34  #SimpNegUnit  : 0
% 2.36/1.34  #BackRed      : 0
% 2.36/1.34  
% 2.36/1.34  #Partial instantiations: 0
% 2.36/1.34  #Strategies tried      : 1
% 2.36/1.34  
% 2.36/1.34  Timing (in seconds)
% 2.36/1.34  ----------------------
% 2.36/1.34  Preprocessing        : 0.28
% 2.36/1.34  Parsing              : 0.14
% 2.36/1.34  CNF conversion       : 0.02
% 2.36/1.34  Main loop            : 0.25
% 2.36/1.34  Inferencing          : 0.10
% 2.36/1.34  Reduction            : 0.07
% 2.36/1.34  Demodulation         : 0.06
% 2.36/1.34  BG Simplification    : 0.02
% 2.36/1.34  Subsumption          : 0.05
% 2.36/1.34  Abstraction          : 0.02
% 2.36/1.34  MUC search           : 0.00
% 2.36/1.34  Cooper               : 0.00
% 2.36/1.34  Total                : 0.55
% 2.36/1.34  Index Insertion      : 0.00
% 2.36/1.34  Index Deletion       : 0.00
% 2.36/1.34  Index Matching       : 0.00
% 2.36/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
