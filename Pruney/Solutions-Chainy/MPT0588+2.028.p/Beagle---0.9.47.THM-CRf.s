%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:06 EST 2020

% Result     : Theorem 4.90s
% Output     : CNFRefutation 5.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  63 expanded)
%              Number of leaves         :   32 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  56 expanded)
%              Number of equality atoms :   31 (  37 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_53,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_29,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(B,C,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_enumset1)).

tff(f_39,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_51,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [A_42] : v1_relat_1(k6_relat_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_46] : k1_relat_1(k6_relat_1(A_46)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_498,plain,(
    ! [B_87,A_88] :
      ( k3_xboole_0(k1_relat_1(B_87),A_88) = k1_relat_1(k7_relat_1(B_87,A_88))
      | ~ v1_relat_1(B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_518,plain,(
    ! [A_46,A_88] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_46),A_88)) = k3_xboole_0(A_46,A_88)
      | ~ v1_relat_1(k6_relat_1(A_46)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_498])).

tff(c_524,plain,(
    ! [A_46,A_88] : k1_relat_1(k7_relat_1(k6_relat_1(A_46),A_88)) = k3_xboole_0(A_46,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_518])).

tff(c_1281,plain,(
    ! [A_134,B_135] :
      ( k7_relat_1(A_134,k1_relat_1(k7_relat_1(B_135,k1_relat_1(A_134)))) = k7_relat_1(A_134,k1_relat_1(B_135))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(A_134) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1304,plain,(
    ! [A_134,A_46] :
      ( k7_relat_1(A_134,k3_xboole_0(A_46,k1_relat_1(A_134))) = k7_relat_1(A_134,k1_relat_1(k6_relat_1(A_46)))
      | ~ v1_relat_1(k6_relat_1(A_46))
      | ~ v1_relat_1(A_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_524,c_1281])).

tff(c_4354,plain,(
    ! [A_195,A_196] :
      ( k7_relat_1(A_195,k3_xboole_0(A_196,k1_relat_1(A_195))) = k7_relat_1(A_195,A_196)
      | ~ v1_relat_1(A_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_32,c_1304])).

tff(c_8,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),k1_tarski(B_13)) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_136,plain,(
    ! [B_61,C_62,A_63] : k1_enumset1(B_61,C_62,A_63) = k1_enumset1(A_63,B_61,C_62) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    ! [A_18,B_19] : k1_enumset1(A_18,A_18,B_19) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_156,plain,(
    ! [A_63,C_62] : k1_enumset1(A_63,C_62,C_62) = k2_tarski(C_62,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_14])).

tff(c_12,plain,(
    ! [A_17] : k2_tarski(A_17,A_17) = k1_tarski(A_17) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_303,plain,(
    ! [A_74,B_75,C_76] : k2_xboole_0(k1_tarski(A_74),k2_tarski(B_75,C_76)) = k1_enumset1(A_74,B_75,C_76) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_312,plain,(
    ! [A_74,A_17] : k2_xboole_0(k1_tarski(A_74),k1_tarski(A_17)) = k1_enumset1(A_74,A_17,A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_303])).

tff(c_316,plain,(
    ! [A_78,A_77] : k2_tarski(A_78,A_77) = k2_tarski(A_77,A_78) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_156,c_312])).

tff(c_26,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_525,plain,(
    ! [A_89,A_90] : k1_setfam_1(k2_tarski(A_89,A_90)) = k3_xboole_0(A_90,A_89) ),
    inference(superposition,[status(thm),theory(equality)],[c_316,c_26])).

tff(c_531,plain,(
    ! [A_90,A_89] : k3_xboole_0(A_90,A_89) = k3_xboole_0(A_89,A_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_525,c_26])).

tff(c_38,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_551,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_531,c_38])).

tff(c_4363,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_4354,c_551])).

tff(c_4400,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_4363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:10:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.90/1.98  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  
% 5.17/1.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/1.99  %$ v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.17/1.99  
% 5.17/1.99  %Foreground sorts:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Background operators:
% 5.17/1.99  
% 5.17/1.99  
% 5.17/1.99  %Foreground operators:
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.17/1.99  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.17/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.17/1.99  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.17/1.99  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.17/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.17/1.99  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.17/1.99  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.17/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.17/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.17/1.99  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.17/1.99  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.17/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.17/1.99  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 5.17/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.17/1.99  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.17/1.99  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.17/1.99  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.17/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.17/1.99  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.17/1.99  
% 5.17/2.00  tff(f_73, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 5.17/2.00  tff(f_53, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 5.17/2.00  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 5.17/2.00  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 5.17/2.00  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t189_relat_1)).
% 5.17/2.00  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_enumset1)).
% 5.17/2.00  tff(f_29, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(B, C, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_enumset1)).
% 5.17/2.00  tff(f_39, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.17/2.00  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.17/2.00  tff(f_35, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 5.17/2.00  tff(f_51, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.17/2.00  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.17/2.00  tff(c_28, plain, (![A_42]: (v1_relat_1(k6_relat_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.17/2.00  tff(c_32, plain, (![A_46]: (k1_relat_1(k6_relat_1(A_46))=A_46)), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.17/2.00  tff(c_498, plain, (![B_87, A_88]: (k3_xboole_0(k1_relat_1(B_87), A_88)=k1_relat_1(k7_relat_1(B_87, A_88)) | ~v1_relat_1(B_87))), inference(cnfTransformation, [status(thm)], [f_68])).
% 5.17/2.00  tff(c_518, plain, (![A_46, A_88]: (k1_relat_1(k7_relat_1(k6_relat_1(A_46), A_88))=k3_xboole_0(A_46, A_88) | ~v1_relat_1(k6_relat_1(A_46)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_498])).
% 5.17/2.00  tff(c_524, plain, (![A_46, A_88]: (k1_relat_1(k7_relat_1(k6_relat_1(A_46), A_88))=k3_xboole_0(A_46, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_518])).
% 5.17/2.00  tff(c_1281, plain, (![A_134, B_135]: (k7_relat_1(A_134, k1_relat_1(k7_relat_1(B_135, k1_relat_1(A_134))))=k7_relat_1(A_134, k1_relat_1(B_135)) | ~v1_relat_1(B_135) | ~v1_relat_1(A_134))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.17/2.00  tff(c_1304, plain, (![A_134, A_46]: (k7_relat_1(A_134, k3_xboole_0(A_46, k1_relat_1(A_134)))=k7_relat_1(A_134, k1_relat_1(k6_relat_1(A_46))) | ~v1_relat_1(k6_relat_1(A_46)) | ~v1_relat_1(A_134))), inference(superposition, [status(thm), theory('equality')], [c_524, c_1281])).
% 5.17/2.00  tff(c_4354, plain, (![A_195, A_196]: (k7_relat_1(A_195, k3_xboole_0(A_196, k1_relat_1(A_195)))=k7_relat_1(A_195, A_196) | ~v1_relat_1(A_195))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_32, c_1304])).
% 5.17/2.00  tff(c_8, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), k1_tarski(B_13))=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.17/2.00  tff(c_136, plain, (![B_61, C_62, A_63]: (k1_enumset1(B_61, C_62, A_63)=k1_enumset1(A_63, B_61, C_62))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.17/2.00  tff(c_14, plain, (![A_18, B_19]: (k1_enumset1(A_18, A_18, B_19)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.17/2.00  tff(c_156, plain, (![A_63, C_62]: (k1_enumset1(A_63, C_62, C_62)=k2_tarski(C_62, A_63))), inference(superposition, [status(thm), theory('equality')], [c_136, c_14])).
% 5.17/2.00  tff(c_12, plain, (![A_17]: (k2_tarski(A_17, A_17)=k1_tarski(A_17))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.17/2.00  tff(c_303, plain, (![A_74, B_75, C_76]: (k2_xboole_0(k1_tarski(A_74), k2_tarski(B_75, C_76))=k1_enumset1(A_74, B_75, C_76))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.17/2.00  tff(c_312, plain, (![A_74, A_17]: (k2_xboole_0(k1_tarski(A_74), k1_tarski(A_17))=k1_enumset1(A_74, A_17, A_17))), inference(superposition, [status(thm), theory('equality')], [c_12, c_303])).
% 5.17/2.00  tff(c_316, plain, (![A_78, A_77]: (k2_tarski(A_78, A_77)=k2_tarski(A_77, A_78))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_156, c_312])).
% 5.17/2.00  tff(c_26, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.17/2.00  tff(c_525, plain, (![A_89, A_90]: (k1_setfam_1(k2_tarski(A_89, A_90))=k3_xboole_0(A_90, A_89))), inference(superposition, [status(thm), theory('equality')], [c_316, c_26])).
% 5.17/2.00  tff(c_531, plain, (![A_90, A_89]: (k3_xboole_0(A_90, A_89)=k3_xboole_0(A_89, A_90))), inference(superposition, [status(thm), theory('equality')], [c_525, c_26])).
% 5.17/2.00  tff(c_38, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_73])).
% 5.17/2.00  tff(c_551, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_531, c_38])).
% 5.17/2.00  tff(c_4363, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_4354, c_551])).
% 5.17/2.00  tff(c_4400, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_4363])).
% 5.17/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.17/2.00  
% 5.17/2.00  Inference rules
% 5.17/2.00  ----------------------
% 5.17/2.00  #Ref     : 0
% 5.17/2.00  #Sup     : 1071
% 5.17/2.00  #Fact    : 0
% 5.17/2.00  #Define  : 0
% 5.17/2.00  #Split   : 0
% 5.17/2.00  #Chain   : 0
% 5.17/2.00  #Close   : 0
% 5.17/2.00  
% 5.17/2.00  Ordering : KBO
% 5.17/2.00  
% 5.17/2.00  Simplification rules
% 5.17/2.00  ----------------------
% 5.17/2.00  #Subsume      : 281
% 5.17/2.00  #Demod        : 723
% 5.17/2.00  #Tautology    : 670
% 5.17/2.00  #SimpNegUnit  : 0
% 5.17/2.00  #BackRed      : 1
% 5.17/2.00  
% 5.17/2.00  #Partial instantiations: 0
% 5.17/2.00  #Strategies tried      : 1
% 5.17/2.00  
% 5.17/2.00  Timing (in seconds)
% 5.17/2.00  ----------------------
% 5.17/2.01  Preprocessing        : 0.34
% 5.17/2.01  Parsing              : 0.19
% 5.17/2.01  CNF conversion       : 0.02
% 5.17/2.01  Main loop            : 0.84
% 5.17/2.01  Inferencing          : 0.29
% 5.17/2.01  Reduction            : 0.40
% 5.17/2.01  Demodulation         : 0.35
% 5.17/2.01  BG Simplification    : 0.03
% 5.17/2.01  Subsumption          : 0.09
% 5.17/2.01  Abstraction          : 0.05
% 5.17/2.01  MUC search           : 0.00
% 5.17/2.01  Cooper               : 0.00
% 5.17/2.01  Total                : 1.22
% 5.17/2.01  Index Insertion      : 0.00
% 5.17/2.01  Index Deletion       : 0.00
% 5.17/2.01  Index Matching       : 0.00
% 5.17/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
