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
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   53 (  88 expanded)
%              Number of leaves         :   28 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   59 ( 121 expanded)
%              Number of equality atoms :   29 (  47 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_147,plain,(
    ! [A_49,B_50] :
      ( k8_relat_1(A_49,B_50) = B_50
      | ~ r1_tarski(k2_relat_1(B_50),A_49)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_158,plain,(
    ! [B_51] :
      ( k8_relat_1(k2_relat_1(B_51),B_51) = B_51
      | ~ v1_relat_1(B_51) ) ),
    inference(resolution,[status(thm)],[c_6,c_147])).

tff(c_100,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [B_16,A_15] :
      ( k5_relat_1(B_16,k6_relat_1(A_15)) = k8_relat_1(A_15,B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_107,plain,(
    ! [A_15,A_40] :
      ( k8_relat_1(A_15,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_15),A_40)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_18])).

tff(c_120,plain,(
    ! [A_15,A_40] : k8_relat_1(A_15,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_15),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_107])).

tff(c_165,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_40))),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_120])).

tff(c_178,plain,(
    ! [A_40] : k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_24,c_165])).

tff(c_315,plain,(
    ! [C_64,A_65,B_66] :
      ( k7_relat_1(k7_relat_1(C_64,A_65),B_66) = k7_relat_1(C_64,k3_xboole_0(A_65,B_66))
      | ~ v1_relat_1(C_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_347,plain,(
    ! [A_40,B_66] :
      ( k7_relat_1(k6_relat_1(A_40),k3_xboole_0(A_40,B_66)) = k7_relat_1(k6_relat_1(A_40),B_66)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_315])).

tff(c_356,plain,(
    ! [A_67,B_68] : k7_relat_1(k6_relat_1(A_67),k3_xboole_0(A_67,B_68)) = k7_relat_1(k6_relat_1(A_67),B_68) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_347])).

tff(c_150,plain,(
    ! [A_49,A_19] :
      ( k8_relat_1(A_49,k6_relat_1(A_19)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_49)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_147])).

tff(c_156,plain,(
    ! [A_49,A_19] :
      ( k7_relat_1(k6_relat_1(A_49),A_19) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_120,c_150])).

tff(c_368,plain,(
    ! [A_67,B_68] :
      ( k7_relat_1(k6_relat_1(A_67),B_68) = k6_relat_1(k3_xboole_0(A_67,B_68))
      | ~ r1_tarski(k3_xboole_0(A_67,B_68),A_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_156])).

tff(c_384,plain,(
    ! [A_67,B_68] : k7_relat_1(k6_relat_1(A_67),B_68) = k6_relat_1(k3_xboole_0(A_67,B_68)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_368])).

tff(c_86,plain,(
    ! [B_38,A_39] :
      ( k5_relat_1(B_38,k6_relat_1(A_39)) = k8_relat_1(A_39,B_38)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_92,plain,
    ( k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_34])).

tff(c_98,plain,(
    k8_relat_1('#skF_1',k6_relat_1('#skF_2')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_92])).

tff(c_126,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_98])).

tff(c_394,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  
% 2.17/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.29  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.17/1.29  
% 2.17/1.29  %Foreground sorts:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Background operators:
% 2.17/1.29  
% 2.17/1.29  
% 2.17/1.29  %Foreground operators:
% 2.17/1.29  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.29  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.17/1.29  
% 2.17/1.30  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.17/1.30  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.17/1.30  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.17/1.30  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.17/1.30  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.17/1.30  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.17/1.30  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.17/1.30  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.17/1.30  tff(f_74, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.17/1.30  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.30  tff(c_30, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.30  tff(c_24, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.30  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.30  tff(c_147, plain, (![A_49, B_50]: (k8_relat_1(A_49, B_50)=B_50 | ~r1_tarski(k2_relat_1(B_50), A_49) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.30  tff(c_158, plain, (![B_51]: (k8_relat_1(k2_relat_1(B_51), B_51)=B_51 | ~v1_relat_1(B_51))), inference(resolution, [status(thm)], [c_6, c_147])).
% 2.17/1.30  tff(c_100, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.17/1.30  tff(c_18, plain, (![B_16, A_15]: (k5_relat_1(B_16, k6_relat_1(A_15))=k8_relat_1(A_15, B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.30  tff(c_107, plain, (![A_15, A_40]: (k8_relat_1(A_15, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_15), A_40) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_18])).
% 2.17/1.30  tff(c_120, plain, (![A_15, A_40]: (k8_relat_1(A_15, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_15), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_107])).
% 2.17/1.30  tff(c_165, plain, (![A_40]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_40))), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_158, c_120])).
% 2.17/1.30  tff(c_178, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_24, c_165])).
% 2.17/1.30  tff(c_315, plain, (![C_64, A_65, B_66]: (k7_relat_1(k7_relat_1(C_64, A_65), B_66)=k7_relat_1(C_64, k3_xboole_0(A_65, B_66)) | ~v1_relat_1(C_64))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.17/1.30  tff(c_347, plain, (![A_40, B_66]: (k7_relat_1(k6_relat_1(A_40), k3_xboole_0(A_40, B_66))=k7_relat_1(k6_relat_1(A_40), B_66) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_178, c_315])).
% 2.17/1.30  tff(c_356, plain, (![A_67, B_68]: (k7_relat_1(k6_relat_1(A_67), k3_xboole_0(A_67, B_68))=k7_relat_1(k6_relat_1(A_67), B_68))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_347])).
% 2.17/1.30  tff(c_150, plain, (![A_49, A_19]: (k8_relat_1(A_49, k6_relat_1(A_19))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_49) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_147])).
% 2.17/1.30  tff(c_156, plain, (![A_49, A_19]: (k7_relat_1(k6_relat_1(A_49), A_19)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_49))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_120, c_150])).
% 2.17/1.30  tff(c_368, plain, (![A_67, B_68]: (k7_relat_1(k6_relat_1(A_67), B_68)=k6_relat_1(k3_xboole_0(A_67, B_68)) | ~r1_tarski(k3_xboole_0(A_67, B_68), A_67))), inference(superposition, [status(thm), theory('equality')], [c_356, c_156])).
% 2.17/1.30  tff(c_384, plain, (![A_67, B_68]: (k7_relat_1(k6_relat_1(A_67), B_68)=k6_relat_1(k3_xboole_0(A_67, B_68)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_368])).
% 2.17/1.30  tff(c_86, plain, (![B_38, A_39]: (k5_relat_1(B_38, k6_relat_1(A_39))=k8_relat_1(A_39, B_38) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.17/1.30  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.17/1.30  tff(c_92, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_34])).
% 2.17/1.30  tff(c_98, plain, (k8_relat_1('#skF_1', k6_relat_1('#skF_2'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_92])).
% 2.17/1.30  tff(c_126, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_120, c_98])).
% 2.17/1.30  tff(c_394, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_384, c_126])).
% 2.17/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.30  
% 2.17/1.30  Inference rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Ref     : 0
% 2.17/1.30  #Sup     : 71
% 2.17/1.30  #Fact    : 0
% 2.17/1.30  #Define  : 0
% 2.17/1.30  #Split   : 2
% 2.17/1.30  #Chain   : 0
% 2.17/1.30  #Close   : 0
% 2.17/1.30  
% 2.17/1.30  Ordering : KBO
% 2.17/1.30  
% 2.17/1.30  Simplification rules
% 2.17/1.30  ----------------------
% 2.17/1.30  #Subsume      : 2
% 2.17/1.30  #Demod        : 53
% 2.17/1.30  #Tautology    : 45
% 2.17/1.30  #SimpNegUnit  : 0
% 2.17/1.30  #BackRed      : 6
% 2.17/1.30  
% 2.17/1.30  #Partial instantiations: 0
% 2.17/1.30  #Strategies tried      : 1
% 2.17/1.30  
% 2.17/1.30  Timing (in seconds)
% 2.17/1.30  ----------------------
% 2.17/1.31  Preprocessing        : 0.31
% 2.17/1.31  Parsing              : 0.16
% 2.17/1.31  CNF conversion       : 0.02
% 2.17/1.31  Main loop            : 0.22
% 2.17/1.31  Inferencing          : 0.08
% 2.17/1.31  Reduction            : 0.07
% 2.17/1.31  Demodulation         : 0.05
% 2.17/1.31  BG Simplification    : 0.02
% 2.17/1.31  Subsumption          : 0.03
% 2.17/1.31  Abstraction          : 0.02
% 2.17/1.31  MUC search           : 0.00
% 2.17/1.31  Cooper               : 0.00
% 2.17/1.31  Total                : 0.55
% 2.17/1.31  Index Insertion      : 0.00
% 2.17/1.31  Index Deletion       : 0.00
% 2.17/1.31  Index Matching       : 0.00
% 2.17/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
