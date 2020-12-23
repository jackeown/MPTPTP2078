%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:06 EST 2020

% Result     : Theorem 3.64s
% Output     : CNFRefutation 3.95s
% Verified   : 
% Statistics : Number of formulae       :   60 (  67 expanded)
%              Number of leaves         :   33 (  37 expanded)
%              Depth                    :   12
%              Number of atoms          :   56 (  65 expanded)
%              Number of equality atoms :   30 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t89_relat_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_27,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_26,plain,(
    ! [A_42,B_43] :
      ( v1_relat_1(k7_relat_1(A_42,B_43))
      | ~ v1_relat_1(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_28,plain,(
    ! [C_46,A_44,B_45] :
      ( k7_relat_1(k7_relat_1(C_46,A_44),B_45) = k7_relat_1(C_46,k3_xboole_0(A_44,B_45))
      | ~ v1_relat_1(C_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [B_48,A_47] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_48,A_47)),k1_relat_1(B_48))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_240,plain,(
    ! [B_75,A_76] :
      ( k7_relat_1(B_75,A_76) = B_75
      | ~ r1_tarski(k1_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1038,plain,(
    ! [B_139,A_140] :
      ( k7_relat_1(k7_relat_1(B_139,A_140),k1_relat_1(B_139)) = k7_relat_1(B_139,A_140)
      | ~ v1_relat_1(k7_relat_1(B_139,A_140))
      | ~ v1_relat_1(B_139) ) ),
    inference(resolution,[status(thm)],[c_30,c_240])).

tff(c_2022,plain,(
    ! [C_172,A_173] :
      ( k7_relat_1(C_172,k3_xboole_0(A_173,k1_relat_1(C_172))) = k7_relat_1(C_172,A_173)
      | ~ v1_relat_1(k7_relat_1(C_172,A_173))
      | ~ v1_relat_1(C_172)
      | ~ v1_relat_1(C_172) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_1038])).

tff(c_6,plain,(
    ! [A_8,B_9] : k2_xboole_0(k1_tarski(A_8),k1_tarski(B_9)) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_114,plain,(
    ! [C_62,B_63,A_64] : k1_enumset1(C_62,B_63,A_64) = k1_enumset1(A_64,B_63,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_11,B_12] : k1_enumset1(A_11,A_11,B_12) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_130,plain,(
    ! [C_62,B_63] : k1_enumset1(C_62,B_63,B_63) = k2_tarski(B_63,C_62) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_10])).

tff(c_8,plain,(
    ! [A_10] : k2_tarski(A_10,A_10) = k1_tarski(A_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_13,B_14,C_15] : k2_enumset1(A_13,A_13,B_14,C_15) = k1_enumset1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_254,plain,(
    ! [A_81,B_82,C_83,D_84] : k2_xboole_0(k2_tarski(A_81,B_82),k2_tarski(C_83,D_84)) = k2_enumset1(A_81,B_82,C_83,D_84) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_271,plain,(
    ! [A_10,C_83,D_84] : k2_xboole_0(k1_tarski(A_10),k2_tarski(C_83,D_84)) = k2_enumset1(A_10,A_10,C_83,D_84) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_254])).

tff(c_278,plain,(
    ! [A_85,C_86,D_87] : k2_xboole_0(k1_tarski(A_85),k2_tarski(C_86,D_87)) = k1_enumset1(A_85,C_86,D_87) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_271])).

tff(c_287,plain,(
    ! [A_85,A_10] : k2_xboole_0(k1_tarski(A_85),k1_tarski(A_10)) = k1_enumset1(A_85,A_10,A_10) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_278])).

tff(c_291,plain,(
    ! [A_89,A_88] : k2_tarski(A_89,A_88) = k2_tarski(A_88,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_130,c_287])).

tff(c_24,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_354,plain,(
    ! [A_90,A_91] : k1_setfam_1(k2_tarski(A_90,A_91)) = k3_xboole_0(A_91,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_24])).

tff(c_360,plain,(
    ! [A_91,A_90] : k3_xboole_0(A_91,A_90) = k3_xboole_0(A_90,A_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_354,c_24])).

tff(c_34,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_401,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_360,c_34])).

tff(c_2044,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_2022,c_401])).

tff(c_2084,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2044])).

tff(c_2088,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_2084])).

tff(c_2092,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.36  % Computer   : n006.cluster.edu
% 0.15/0.36  % Model      : x86_64 x86_64
% 0.15/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.36  % Memory     : 8042.1875MB
% 0.15/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.36  % CPULimit   : 60
% 0.15/0.36  % DateTime   : Tue Dec  1 10:10:07 EST 2020
% 0.15/0.36  % CPUTime    : 
% 0.15/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.64/1.62  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.63  
% 3.64/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.64/1.63  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.64/1.63  
% 3.64/1.63  %Foreground sorts:
% 3.64/1.63  
% 3.64/1.63  
% 3.64/1.63  %Background operators:
% 3.64/1.63  
% 3.64/1.63  
% 3.64/1.63  %Foreground operators:
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.64/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.64/1.63  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.64/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.64/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.64/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.64/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.64/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.64/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.64/1.63  tff('#skF_1', type, '#skF_1': $i).
% 3.64/1.63  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.63  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.64/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.64/1.63  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.64/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.64/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.64/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.64/1.63  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.64/1.63  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.64/1.63  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.64/1.63  
% 3.95/1.64  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.95/1.64  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.95/1.64  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.95/1.64  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t89_relat_1)).
% 3.95/1.64  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.95/1.64  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 3.95/1.64  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.95/1.64  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.95/1.64  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.95/1.64  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.95/1.64  tff(f_27, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 3.95/1.64  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.95/1.64  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.95/1.64  tff(c_26, plain, (![A_42, B_43]: (v1_relat_1(k7_relat_1(A_42, B_43)) | ~v1_relat_1(A_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.95/1.64  tff(c_28, plain, (![C_46, A_44, B_45]: (k7_relat_1(k7_relat_1(C_46, A_44), B_45)=k7_relat_1(C_46, k3_xboole_0(A_44, B_45)) | ~v1_relat_1(C_46))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.95/1.64  tff(c_30, plain, (![B_48, A_47]: (r1_tarski(k1_relat_1(k7_relat_1(B_48, A_47)), k1_relat_1(B_48)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.95/1.64  tff(c_240, plain, (![B_75, A_76]: (k7_relat_1(B_75, A_76)=B_75 | ~r1_tarski(k1_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.95/1.64  tff(c_1038, plain, (![B_139, A_140]: (k7_relat_1(k7_relat_1(B_139, A_140), k1_relat_1(B_139))=k7_relat_1(B_139, A_140) | ~v1_relat_1(k7_relat_1(B_139, A_140)) | ~v1_relat_1(B_139))), inference(resolution, [status(thm)], [c_30, c_240])).
% 3.95/1.64  tff(c_2022, plain, (![C_172, A_173]: (k7_relat_1(C_172, k3_xboole_0(A_173, k1_relat_1(C_172)))=k7_relat_1(C_172, A_173) | ~v1_relat_1(k7_relat_1(C_172, A_173)) | ~v1_relat_1(C_172) | ~v1_relat_1(C_172))), inference(superposition, [status(thm), theory('equality')], [c_28, c_1038])).
% 3.95/1.64  tff(c_6, plain, (![A_8, B_9]: (k2_xboole_0(k1_tarski(A_8), k1_tarski(B_9))=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.95/1.64  tff(c_114, plain, (![C_62, B_63, A_64]: (k1_enumset1(C_62, B_63, A_64)=k1_enumset1(A_64, B_63, C_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.95/1.64  tff(c_10, plain, (![A_11, B_12]: (k1_enumset1(A_11, A_11, B_12)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.95/1.64  tff(c_130, plain, (![C_62, B_63]: (k1_enumset1(C_62, B_63, B_63)=k2_tarski(B_63, C_62))), inference(superposition, [status(thm), theory('equality')], [c_114, c_10])).
% 3.95/1.64  tff(c_8, plain, (![A_10]: (k2_tarski(A_10, A_10)=k1_tarski(A_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.95/1.64  tff(c_12, plain, (![A_13, B_14, C_15]: (k2_enumset1(A_13, A_13, B_14, C_15)=k1_enumset1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.95/1.64  tff(c_254, plain, (![A_81, B_82, C_83, D_84]: (k2_xboole_0(k2_tarski(A_81, B_82), k2_tarski(C_83, D_84))=k2_enumset1(A_81, B_82, C_83, D_84))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.95/1.64  tff(c_271, plain, (![A_10, C_83, D_84]: (k2_xboole_0(k1_tarski(A_10), k2_tarski(C_83, D_84))=k2_enumset1(A_10, A_10, C_83, D_84))), inference(superposition, [status(thm), theory('equality')], [c_8, c_254])).
% 3.95/1.64  tff(c_278, plain, (![A_85, C_86, D_87]: (k2_xboole_0(k1_tarski(A_85), k2_tarski(C_86, D_87))=k1_enumset1(A_85, C_86, D_87))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_271])).
% 3.95/1.64  tff(c_287, plain, (![A_85, A_10]: (k2_xboole_0(k1_tarski(A_85), k1_tarski(A_10))=k1_enumset1(A_85, A_10, A_10))), inference(superposition, [status(thm), theory('equality')], [c_8, c_278])).
% 3.95/1.64  tff(c_291, plain, (![A_89, A_88]: (k2_tarski(A_89, A_88)=k2_tarski(A_88, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_130, c_287])).
% 3.95/1.64  tff(c_24, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.95/1.64  tff(c_354, plain, (![A_90, A_91]: (k1_setfam_1(k2_tarski(A_90, A_91))=k3_xboole_0(A_91, A_90))), inference(superposition, [status(thm), theory('equality')], [c_291, c_24])).
% 3.95/1.64  tff(c_360, plain, (![A_91, A_90]: (k3_xboole_0(A_91, A_90)=k3_xboole_0(A_90, A_91))), inference(superposition, [status(thm), theory('equality')], [c_354, c_24])).
% 3.95/1.64  tff(c_34, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.95/1.64  tff(c_401, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_360, c_34])).
% 3.95/1.64  tff(c_2044, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_2022, c_401])).
% 3.95/1.64  tff(c_2084, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_2044])).
% 3.95/1.64  tff(c_2088, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_26, c_2084])).
% 3.95/1.64  tff(c_2092, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2088])).
% 3.95/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.95/1.64  
% 3.95/1.64  Inference rules
% 3.95/1.64  ----------------------
% 3.95/1.64  #Ref     : 0
% 3.95/1.64  #Sup     : 515
% 3.95/1.64  #Fact    : 0
% 3.95/1.64  #Define  : 0
% 3.95/1.64  #Split   : 0
% 3.95/1.64  #Chain   : 0
% 3.95/1.64  #Close   : 0
% 3.95/1.64  
% 3.95/1.64  Ordering : KBO
% 3.95/1.64  
% 3.95/1.64  Simplification rules
% 3.95/1.64  ----------------------
% 3.95/1.64  #Subsume      : 96
% 3.95/1.64  #Demod        : 268
% 3.95/1.64  #Tautology    : 316
% 3.95/1.64  #SimpNegUnit  : 0
% 3.95/1.64  #BackRed      : 2
% 3.95/1.64  
% 3.95/1.64  #Partial instantiations: 0
% 3.95/1.64  #Strategies tried      : 1
% 3.95/1.64  
% 3.95/1.64  Timing (in seconds)
% 3.95/1.64  ----------------------
% 3.95/1.64  Preprocessing        : 0.33
% 3.95/1.64  Parsing              : 0.18
% 3.95/1.64  CNF conversion       : 0.02
% 3.95/1.64  Main loop            : 0.54
% 3.95/1.64  Inferencing          : 0.20
% 3.95/1.64  Reduction            : 0.21
% 3.95/1.64  Demodulation         : 0.18
% 3.95/1.64  BG Simplification    : 0.03
% 3.95/1.64  Subsumption          : 0.07
% 3.95/1.64  Abstraction          : 0.03
% 3.95/1.64  MUC search           : 0.00
% 3.95/1.64  Cooper               : 0.00
% 3.95/1.64  Total                : 0.89
% 3.95/1.65  Index Insertion      : 0.00
% 3.95/1.65  Index Deletion       : 0.00
% 3.95/1.65  Index Matching       : 0.00
% 3.95/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------
