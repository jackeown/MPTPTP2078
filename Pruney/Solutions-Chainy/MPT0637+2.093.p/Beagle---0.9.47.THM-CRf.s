%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   52 (  64 expanded)
%              Number of leaves         :   28 (  35 expanded)
%              Depth                    :    8
%              Number of atoms          :   57 (  76 expanded)
%              Number of equality atoms :   29 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [A_17] : k1_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_50,plain,(
    ! [A_28] :
      ( k7_relat_1(A_28,k1_relat_1(A_28)) = A_28
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_59,plain,(
    ! [A_17] :
      ( k7_relat_1(k6_relat_1(A_17),A_17) = k6_relat_1(A_17)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_63,plain,(
    ! [A_17] : k7_relat_1(k6_relat_1(A_17),A_17) = k6_relat_1(A_17) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_59])).

tff(c_191,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(k7_relat_1(C_47,A_48),B_49) = k7_relat_1(C_47,k3_xboole_0(A_48,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [A_17,B_49] :
      ( k7_relat_1(k6_relat_1(A_17),k3_xboole_0(A_17,B_49)) = k7_relat_1(k6_relat_1(A_17),B_49)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_191])).

tff(c_227,plain,(
    ! [A_50,B_51] : k7_relat_1(k6_relat_1(A_50),k3_xboole_0(A_50,B_51)) = k7_relat_1(k6_relat_1(A_50),B_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_213])).

tff(c_114,plain,(
    ! [B_39,A_40] :
      ( k5_relat_1(B_39,k6_relat_1(A_40)) = k8_relat_1(A_40,B_39)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_121,plain,(
    ! [A_40,A_18] :
      ( k8_relat_1(A_40,k6_relat_1(A_18)) = k7_relat_1(k6_relat_1(A_40),A_18)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_20])).

tff(c_134,plain,(
    ! [A_40,A_18] : k8_relat_1(A_40,k6_relat_1(A_18)) = k7_relat_1(k6_relat_1(A_40),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_121])).

tff(c_18,plain,(
    ! [A_17] : k2_relat_1(k6_relat_1(A_17)) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_149,plain,(
    ! [A_43,B_44] :
      ( k8_relat_1(A_43,B_44) = B_44
      | ~ r1_tarski(k2_relat_1(B_44),A_43)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_152,plain,(
    ! [A_43,A_17] :
      ( k8_relat_1(A_43,k6_relat_1(A_17)) = k6_relat_1(A_17)
      | ~ r1_tarski(A_17,A_43)
      | ~ v1_relat_1(k6_relat_1(A_17)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_149])).

tff(c_154,plain,(
    ! [A_43,A_17] :
      ( k7_relat_1(k6_relat_1(A_43),A_17) = k6_relat_1(A_17)
      | ~ r1_tarski(A_17,A_43) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_134,c_152])).

tff(c_236,plain,(
    ! [A_50,B_51] :
      ( k7_relat_1(k6_relat_1(A_50),B_51) = k6_relat_1(k3_xboole_0(A_50,B_51))
      | ~ r1_tarski(k3_xboole_0(A_50,B_51),A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_154])).

tff(c_248,plain,(
    ! [A_50,B_51] : k7_relat_1(k6_relat_1(A_50),B_51) = k6_relat_1(k3_xboole_0(A_50,B_51)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_100,plain,(
    ! [A_37,B_38] :
      ( k5_relat_1(k6_relat_1(A_37),B_38) = k7_relat_1(B_38,A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_28,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_106,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_28])).

tff(c_112,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_106])).

tff(c_257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:28:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  
% 1.97/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.21  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.97/1.21  
% 1.97/1.21  %Foreground sorts:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Background operators:
% 1.97/1.21  
% 1.97/1.21  
% 1.97/1.21  %Foreground operators:
% 1.97/1.21  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.97/1.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.97/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.97/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.97/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.97/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.97/1.21  
% 1.97/1.22  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.97/1.22  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 1.97/1.22  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.97/1.22  tff(f_59, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.97/1.22  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.97/1.22  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 1.97/1.22  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.97/1.22  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 1.97/1.22  tff(f_66, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.97/1.22  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.22  tff(c_24, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.97/1.22  tff(c_16, plain, (![A_17]: (k1_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_50, plain, (![A_28]: (k7_relat_1(A_28, k1_relat_1(A_28))=A_28 | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.97/1.22  tff(c_59, plain, (![A_17]: (k7_relat_1(k6_relat_1(A_17), A_17)=k6_relat_1(A_17) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_50])).
% 1.97/1.22  tff(c_63, plain, (![A_17]: (k7_relat_1(k6_relat_1(A_17), A_17)=k6_relat_1(A_17))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_59])).
% 1.97/1.22  tff(c_191, plain, (![C_47, A_48, B_49]: (k7_relat_1(k7_relat_1(C_47, A_48), B_49)=k7_relat_1(C_47, k3_xboole_0(A_48, B_49)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.97/1.22  tff(c_213, plain, (![A_17, B_49]: (k7_relat_1(k6_relat_1(A_17), k3_xboole_0(A_17, B_49))=k7_relat_1(k6_relat_1(A_17), B_49) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_63, c_191])).
% 1.97/1.22  tff(c_227, plain, (![A_50, B_51]: (k7_relat_1(k6_relat_1(A_50), k3_xboole_0(A_50, B_51))=k7_relat_1(k6_relat_1(A_50), B_51))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_213])).
% 1.97/1.22  tff(c_114, plain, (![B_39, A_40]: (k5_relat_1(B_39, k6_relat_1(A_40))=k8_relat_1(A_40, B_39) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.97/1.22  tff(c_20, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.22  tff(c_121, plain, (![A_40, A_18]: (k8_relat_1(A_40, k6_relat_1(A_18))=k7_relat_1(k6_relat_1(A_40), A_18) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_114, c_20])).
% 1.97/1.22  tff(c_134, plain, (![A_40, A_18]: (k8_relat_1(A_40, k6_relat_1(A_18))=k7_relat_1(k6_relat_1(A_40), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_121])).
% 1.97/1.22  tff(c_18, plain, (![A_17]: (k2_relat_1(k6_relat_1(A_17))=A_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.97/1.22  tff(c_149, plain, (![A_43, B_44]: (k8_relat_1(A_43, B_44)=B_44 | ~r1_tarski(k2_relat_1(B_44), A_43) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.97/1.22  tff(c_152, plain, (![A_43, A_17]: (k8_relat_1(A_43, k6_relat_1(A_17))=k6_relat_1(A_17) | ~r1_tarski(A_17, A_43) | ~v1_relat_1(k6_relat_1(A_17)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_149])).
% 1.97/1.23  tff(c_154, plain, (![A_43, A_17]: (k7_relat_1(k6_relat_1(A_43), A_17)=k6_relat_1(A_17) | ~r1_tarski(A_17, A_43))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_134, c_152])).
% 1.97/1.23  tff(c_236, plain, (![A_50, B_51]: (k7_relat_1(k6_relat_1(A_50), B_51)=k6_relat_1(k3_xboole_0(A_50, B_51)) | ~r1_tarski(k3_xboole_0(A_50, B_51), A_50))), inference(superposition, [status(thm), theory('equality')], [c_227, c_154])).
% 1.97/1.23  tff(c_248, plain, (![A_50, B_51]: (k7_relat_1(k6_relat_1(A_50), B_51)=k6_relat_1(k3_xboole_0(A_50, B_51)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_236])).
% 1.97/1.23  tff(c_100, plain, (![A_37, B_38]: (k5_relat_1(k6_relat_1(A_37), B_38)=k7_relat_1(B_38, A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.97/1.23  tff(c_28, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.97/1.23  tff(c_106, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_100, c_28])).
% 1.97/1.23  tff(c_112, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_106])).
% 1.97/1.23  tff(c_257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_112])).
% 1.97/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.23  
% 1.97/1.23  Inference rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Ref     : 0
% 1.97/1.23  #Sup     : 47
% 1.97/1.23  #Fact    : 0
% 1.97/1.23  #Define  : 0
% 1.97/1.23  #Split   : 1
% 1.97/1.23  #Chain   : 0
% 1.97/1.23  #Close   : 0
% 1.97/1.23  
% 1.97/1.23  Ordering : KBO
% 1.97/1.23  
% 1.97/1.23  Simplification rules
% 1.97/1.23  ----------------------
% 1.97/1.23  #Subsume      : 1
% 1.97/1.23  #Demod        : 26
% 1.97/1.23  #Tautology    : 31
% 1.97/1.23  #SimpNegUnit  : 0
% 1.97/1.23  #BackRed      : 4
% 1.97/1.23  
% 1.97/1.23  #Partial instantiations: 0
% 1.97/1.23  #Strategies tried      : 1
% 1.97/1.23  
% 1.97/1.23  Timing (in seconds)
% 1.97/1.23  ----------------------
% 2.07/1.23  Preprocessing        : 0.30
% 2.07/1.23  Parsing              : 0.17
% 2.07/1.23  CNF conversion       : 0.02
% 2.07/1.23  Main loop            : 0.16
% 2.07/1.23  Inferencing          : 0.07
% 2.07/1.23  Reduction            : 0.05
% 2.07/1.23  Demodulation         : 0.04
% 2.07/1.23  BG Simplification    : 0.01
% 2.07/1.23  Subsumption          : 0.02
% 2.07/1.23  Abstraction          : 0.01
% 2.07/1.23  MUC search           : 0.00
% 2.07/1.23  Cooper               : 0.00
% 2.07/1.23  Total                : 0.49
% 2.07/1.23  Index Insertion      : 0.00
% 2.07/1.23  Index Deletion       : 0.00
% 2.07/1.23  Index Matching       : 0.00
% 2.07/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
