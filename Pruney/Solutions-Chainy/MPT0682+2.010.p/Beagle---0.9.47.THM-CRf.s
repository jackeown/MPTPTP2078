%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:30 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   48 (  62 expanded)
%              Number of leaves         :   29 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  70 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => k9_relat_1(k8_relat_1(A,C),B) = k3_xboole_0(A,k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t126_funct_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_63,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k9_relat_1(k5_relat_1(B,C),A) = k9_relat_1(C,k9_relat_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t159_relat_1)).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    ! [A_23] : v1_relat_1(k6_relat_1(A_23)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_33] : k2_relat_1(k6_relat_1(A_33)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_88,plain,(
    ! [B_48,A_49] :
      ( k5_relat_1(B_48,k6_relat_1(A_49)) = k8_relat_1(A_49,B_48)
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_26,plain,(
    ! [B_35,A_34] : k5_relat_1(k6_relat_1(B_35),k6_relat_1(A_34)) = k6_relat_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_95,plain,(
    ! [A_49,B_35] :
      ( k8_relat_1(A_49,k6_relat_1(B_35)) = k6_relat_1(k3_xboole_0(A_49,B_35))
      | ~ v1_relat_1(k6_relat_1(B_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_26])).

tff(c_104,plain,(
    ! [A_49,B_35] : k8_relat_1(A_49,k6_relat_1(B_35)) = k6_relat_1(k3_xboole_0(A_49,B_35)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_95])).

tff(c_16,plain,(
    ! [B_25,A_24] :
      ( k5_relat_1(B_25,k6_relat_1(A_24)) = k8_relat_1(A_24,B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_127,plain,(
    ! [B_56,A_57] :
      ( k9_relat_1(B_56,k2_relat_1(A_57)) = k2_relat_1(k5_relat_1(A_57,B_56))
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_136,plain,(
    ! [A_33,B_56] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_33),B_56)) = k9_relat_1(B_56,A_33)
      | ~ v1_relat_1(B_56)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_127])).

tff(c_150,plain,(
    ! [A_63,B_64] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_63),B_64)) = k9_relat_1(B_64,A_63)
      | ~ v1_relat_1(B_64) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_163,plain,(
    ! [A_24,A_63] :
      ( k2_relat_1(k8_relat_1(A_24,k6_relat_1(A_63))) = k9_relat_1(k6_relat_1(A_24),A_63)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(k6_relat_1(A_63)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_150])).

tff(c_170,plain,(
    ! [A_24,A_63] : k9_relat_1(k6_relat_1(A_24),A_63) = k3_xboole_0(A_24,A_63) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_24,c_104,c_163])).

tff(c_195,plain,(
    ! [B_67,C_68,A_69] :
      ( k9_relat_1(k5_relat_1(B_67,C_68),A_69) = k9_relat_1(C_68,k9_relat_1(B_67,A_69))
      | ~ v1_relat_1(C_68)
      | ~ v1_relat_1(B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_212,plain,(
    ! [A_24,B_25,A_69] :
      ( k9_relat_1(k6_relat_1(A_24),k9_relat_1(B_25,A_69)) = k9_relat_1(k8_relat_1(A_24,B_25),A_69)
      | ~ v1_relat_1(k6_relat_1(A_24))
      | ~ v1_relat_1(B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_195])).

tff(c_271,plain,(
    ! [A_75,B_76,A_77] :
      ( k9_relat_1(k8_relat_1(A_75,B_76),A_77) = k3_xboole_0(A_75,k9_relat_1(B_76,A_77))
      | ~ v1_relat_1(B_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_170,c_212])).

tff(c_28,plain,(
    k9_relat_1(k8_relat_1('#skF_1','#skF_3'),'#skF_2') != k3_xboole_0('#skF_1',k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_281,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_28])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:59:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  %$ v1_relat_1 > v1_funct_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k8_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 1.93/1.22  
% 1.93/1.22  %Foreground sorts:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Background operators:
% 1.93/1.22  
% 1.93/1.22  
% 1.93/1.22  %Foreground operators:
% 1.93/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.22  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.93/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.93/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.93/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.93/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.93/1.22  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.93/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.93/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.93/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.93/1.22  
% 2.14/1.23  tff(f_70, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k9_relat_1(k8_relat_1(A, C), B) = k3_xboole_0(A, k9_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t126_funct_1)).
% 2.14/1.23  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.14/1.23  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.14/1.23  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.14/1.23  tff(f_63, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.14/1.23  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 2.14/1.23  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k9_relat_1(k5_relat_1(B, C), A) = k9_relat_1(C, k9_relat_1(B, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t159_relat_1)).
% 2.14/1.23  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.23  tff(c_14, plain, (![A_23]: (v1_relat_1(k6_relat_1(A_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.23  tff(c_24, plain, (![A_33]: (k2_relat_1(k6_relat_1(A_33))=A_33)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.14/1.23  tff(c_88, plain, (![B_48, A_49]: (k5_relat_1(B_48, k6_relat_1(A_49))=k8_relat_1(A_49, B_48) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.23  tff(c_26, plain, (![B_35, A_34]: (k5_relat_1(k6_relat_1(B_35), k6_relat_1(A_34))=k6_relat_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.14/1.23  tff(c_95, plain, (![A_49, B_35]: (k8_relat_1(A_49, k6_relat_1(B_35))=k6_relat_1(k3_xboole_0(A_49, B_35)) | ~v1_relat_1(k6_relat_1(B_35)))), inference(superposition, [status(thm), theory('equality')], [c_88, c_26])).
% 2.14/1.23  tff(c_104, plain, (![A_49, B_35]: (k8_relat_1(A_49, k6_relat_1(B_35))=k6_relat_1(k3_xboole_0(A_49, B_35)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_95])).
% 2.14/1.23  tff(c_16, plain, (![B_25, A_24]: (k5_relat_1(B_25, k6_relat_1(A_24))=k8_relat_1(A_24, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.14/1.23  tff(c_127, plain, (![B_56, A_57]: (k9_relat_1(B_56, k2_relat_1(A_57))=k2_relat_1(k5_relat_1(A_57, B_56)) | ~v1_relat_1(B_56) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.23  tff(c_136, plain, (![A_33, B_56]: (k2_relat_1(k5_relat_1(k6_relat_1(A_33), B_56))=k9_relat_1(B_56, A_33) | ~v1_relat_1(B_56) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_127])).
% 2.14/1.23  tff(c_150, plain, (![A_63, B_64]: (k2_relat_1(k5_relat_1(k6_relat_1(A_63), B_64))=k9_relat_1(B_64, A_63) | ~v1_relat_1(B_64))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 2.14/1.23  tff(c_163, plain, (![A_24, A_63]: (k2_relat_1(k8_relat_1(A_24, k6_relat_1(A_63)))=k9_relat_1(k6_relat_1(A_24), A_63) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(k6_relat_1(A_63)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_150])).
% 2.14/1.23  tff(c_170, plain, (![A_24, A_63]: (k9_relat_1(k6_relat_1(A_24), A_63)=k3_xboole_0(A_24, A_63))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_24, c_104, c_163])).
% 2.14/1.23  tff(c_195, plain, (![B_67, C_68, A_69]: (k9_relat_1(k5_relat_1(B_67, C_68), A_69)=k9_relat_1(C_68, k9_relat_1(B_67, A_69)) | ~v1_relat_1(C_68) | ~v1_relat_1(B_67))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.14/1.23  tff(c_212, plain, (![A_24, B_25, A_69]: (k9_relat_1(k6_relat_1(A_24), k9_relat_1(B_25, A_69))=k9_relat_1(k8_relat_1(A_24, B_25), A_69) | ~v1_relat_1(k6_relat_1(A_24)) | ~v1_relat_1(B_25) | ~v1_relat_1(B_25))), inference(superposition, [status(thm), theory('equality')], [c_16, c_195])).
% 2.14/1.23  tff(c_271, plain, (![A_75, B_76, A_77]: (k9_relat_1(k8_relat_1(A_75, B_76), A_77)=k3_xboole_0(A_75, k9_relat_1(B_76, A_77)) | ~v1_relat_1(B_76))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_170, c_212])).
% 2.14/1.23  tff(c_28, plain, (k9_relat_1(k8_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k3_xboole_0('#skF_1', k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.14/1.23  tff(c_281, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_271, c_28])).
% 2.14/1.23  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_281])).
% 2.14/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.23  
% 2.14/1.23  Inference rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Ref     : 0
% 2.14/1.23  #Sup     : 57
% 2.14/1.23  #Fact    : 0
% 2.14/1.23  #Define  : 0
% 2.14/1.23  #Split   : 0
% 2.14/1.23  #Chain   : 0
% 2.14/1.23  #Close   : 0
% 2.14/1.23  
% 2.14/1.23  Ordering : KBO
% 2.14/1.23  
% 2.14/1.23  Simplification rules
% 2.14/1.23  ----------------------
% 2.14/1.23  #Subsume      : 1
% 2.14/1.23  #Demod        : 38
% 2.14/1.23  #Tautology    : 40
% 2.14/1.23  #SimpNegUnit  : 0
% 2.14/1.23  #BackRed      : 0
% 2.14/1.23  
% 2.14/1.23  #Partial instantiations: 0
% 2.14/1.23  #Strategies tried      : 1
% 2.14/1.23  
% 2.14/1.23  Timing (in seconds)
% 2.14/1.23  ----------------------
% 2.14/1.24  Preprocessing        : 0.30
% 2.14/1.24  Parsing              : 0.16
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.16
% 2.14/1.24  Inferencing          : 0.07
% 2.14/1.24  Reduction            : 0.05
% 2.14/1.24  Demodulation         : 0.04
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.02
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.49
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
