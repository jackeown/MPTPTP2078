%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:41 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :   56 (  66 expanded)
%              Number of leaves         :   34 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 (  69 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_69,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_59,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_81,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_56,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_32,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,(
    ! [A_33] : v1_relat_1(k6_relat_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_339,plain,(
    ! [A_99,B_100] :
      ( k5_relat_1(k6_relat_1(A_99),B_100) = k7_relat_1(B_100,A_99)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_40,plain,(
    ! [B_42,A_41] : k5_relat_1(k6_relat_1(B_42),k6_relat_1(A_41)) = k6_relat_1(k3_xboole_0(A_41,B_42)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_346,plain,(
    ! [A_41,A_99] :
      ( k7_relat_1(k6_relat_1(A_41),A_99) = k6_relat_1(k3_xboole_0(A_41,A_99))
      | ~ v1_relat_1(k6_relat_1(A_41)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_339,c_40])).

tff(c_355,plain,(
    ! [A_41,A_99] : k7_relat_1(k6_relat_1(A_41),A_99) = k6_relat_1(k3_xboole_0(A_41,A_99)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_346])).

tff(c_690,plain,(
    ! [B_127,A_128] :
      ( k7_relat_1(B_127,A_128) = B_127
      | ~ r1_tarski(k1_relat_1(B_127),A_128)
      | ~ v1_relat_1(B_127) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_716,plain,(
    ! [A_36,A_128] :
      ( k7_relat_1(k6_relat_1(A_36),A_128) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_128)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_690])).

tff(c_1341,plain,(
    ! [A_157,A_158] :
      ( k6_relat_1(k3_xboole_0(A_157,A_158)) = k6_relat_1(A_157)
      | ~ r1_tarski(A_157,A_158) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_355,c_716])).

tff(c_1401,plain,(
    ! [A_157,A_158] :
      ( k3_xboole_0(A_157,A_158) = k1_relat_1(k6_relat_1(A_157))
      | ~ r1_tarski(A_157,A_158) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1341,c_32])).

tff(c_1457,plain,(
    ! [A_161,A_162] :
      ( k3_xboole_0(A_161,A_162) = A_161
      | ~ r1_tarski(A_161,A_162) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1401])).

tff(c_1512,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_56,c_1457])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1283,plain,(
    ! [C_154,A_155,B_156] :
      ( k2_wellord1(k2_wellord1(C_154,A_155),B_156) = k2_wellord1(C_154,k3_xboole_0(A_155,B_156))
      | ~ v1_relat_1(C_154) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1038,plain,(
    ! [C_142,B_143,A_144] :
      ( k2_wellord1(k2_wellord1(C_142,B_143),A_144) = k2_wellord1(k2_wellord1(C_142,A_144),B_143)
      | ~ v1_relat_1(C_142) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_54,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1077,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1038,c_54])).

tff(c_1116,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1077])).

tff(c_1292,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1283,c_1116])).

tff(c_1337,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1292])).

tff(c_1515,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1512,c_1337])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.59  
% 3.22/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.59  %$ r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k3_tarski > k3_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.22/1.59  
% 3.22/1.59  %Foreground sorts:
% 3.22/1.59  
% 3.22/1.59  
% 3.22/1.59  %Background operators:
% 3.22/1.59  
% 3.22/1.59  
% 3.22/1.59  %Foreground operators:
% 3.22/1.59  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 3.22/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.22/1.59  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.22/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.59  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 3.22/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.22/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.22/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.22/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.22/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.22/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.22/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.22/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.22/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.22/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.22/1.59  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 3.22/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.22/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.22/1.59  
% 3.22/1.60  tff(f_110, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_wellord1)).
% 3.22/1.60  tff(f_69, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.22/1.60  tff(f_59, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.22/1.60  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 3.22/1.60  tff(f_81, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 3.22/1.60  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.22/1.60  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 3.22/1.60  tff(f_103, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_wellord1)).
% 3.22/1.60  tff(c_56, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.22/1.60  tff(c_32, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.22/1.60  tff(c_28, plain, (![A_33]: (v1_relat_1(k6_relat_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.22/1.60  tff(c_339, plain, (![A_99, B_100]: (k5_relat_1(k6_relat_1(A_99), B_100)=k7_relat_1(B_100, A_99) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.22/1.60  tff(c_40, plain, (![B_42, A_41]: (k5_relat_1(k6_relat_1(B_42), k6_relat_1(A_41))=k6_relat_1(k3_xboole_0(A_41, B_42)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.22/1.60  tff(c_346, plain, (![A_41, A_99]: (k7_relat_1(k6_relat_1(A_41), A_99)=k6_relat_1(k3_xboole_0(A_41, A_99)) | ~v1_relat_1(k6_relat_1(A_41)))), inference(superposition, [status(thm), theory('equality')], [c_339, c_40])).
% 3.22/1.60  tff(c_355, plain, (![A_41, A_99]: (k7_relat_1(k6_relat_1(A_41), A_99)=k6_relat_1(k3_xboole_0(A_41, A_99)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_346])).
% 3.22/1.60  tff(c_690, plain, (![B_127, A_128]: (k7_relat_1(B_127, A_128)=B_127 | ~r1_tarski(k1_relat_1(B_127), A_128) | ~v1_relat_1(B_127))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.22/1.60  tff(c_716, plain, (![A_36, A_128]: (k7_relat_1(k6_relat_1(A_36), A_128)=k6_relat_1(A_36) | ~r1_tarski(A_36, A_128) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_690])).
% 3.22/1.60  tff(c_1341, plain, (![A_157, A_158]: (k6_relat_1(k3_xboole_0(A_157, A_158))=k6_relat_1(A_157) | ~r1_tarski(A_157, A_158))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_355, c_716])).
% 3.22/1.60  tff(c_1401, plain, (![A_157, A_158]: (k3_xboole_0(A_157, A_158)=k1_relat_1(k6_relat_1(A_157)) | ~r1_tarski(A_157, A_158))), inference(superposition, [status(thm), theory('equality')], [c_1341, c_32])).
% 3.22/1.60  tff(c_1457, plain, (![A_161, A_162]: (k3_xboole_0(A_161, A_162)=A_161 | ~r1_tarski(A_161, A_162))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1401])).
% 3.22/1.60  tff(c_1512, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_56, c_1457])).
% 3.22/1.60  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.22/1.60  tff(c_1283, plain, (![C_154, A_155, B_156]: (k2_wellord1(k2_wellord1(C_154, A_155), B_156)=k2_wellord1(C_154, k3_xboole_0(A_155, B_156)) | ~v1_relat_1(C_154))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.22/1.60  tff(c_1038, plain, (![C_142, B_143, A_144]: (k2_wellord1(k2_wellord1(C_142, B_143), A_144)=k2_wellord1(k2_wellord1(C_142, A_144), B_143) | ~v1_relat_1(C_142))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.22/1.60  tff(c_54, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.22/1.60  tff(c_1077, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1038, c_54])).
% 3.22/1.60  tff(c_1116, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1077])).
% 3.22/1.60  tff(c_1292, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1283, c_1116])).
% 3.22/1.60  tff(c_1337, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1292])).
% 3.22/1.60  tff(c_1515, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1512, c_1337])).
% 3.22/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.60  
% 3.22/1.60  Inference rules
% 3.22/1.60  ----------------------
% 3.22/1.60  #Ref     : 0
% 3.22/1.60  #Sup     : 347
% 3.22/1.60  #Fact    : 0
% 3.22/1.60  #Define  : 0
% 3.22/1.60  #Split   : 1
% 3.22/1.60  #Chain   : 0
% 3.22/1.60  #Close   : 0
% 3.22/1.60  
% 3.22/1.60  Ordering : KBO
% 3.22/1.60  
% 3.22/1.60  Simplification rules
% 3.22/1.60  ----------------------
% 3.22/1.60  #Subsume      : 20
% 3.22/1.60  #Demod        : 196
% 3.22/1.60  #Tautology    : 141
% 3.22/1.60  #SimpNegUnit  : 0
% 3.22/1.60  #BackRed      : 1
% 3.22/1.60  
% 3.22/1.60  #Partial instantiations: 0
% 3.22/1.60  #Strategies tried      : 1
% 3.22/1.60  
% 3.22/1.60  Timing (in seconds)
% 3.22/1.60  ----------------------
% 3.22/1.60  Preprocessing        : 0.45
% 3.22/1.60  Parsing              : 0.25
% 3.22/1.60  CNF conversion       : 0.03
% 3.22/1.60  Main loop            : 0.46
% 3.22/1.60  Inferencing          : 0.16
% 3.22/1.60  Reduction            : 0.16
% 3.22/1.60  Demodulation         : 0.12
% 3.22/1.60  BG Simplification    : 0.03
% 3.22/1.60  Subsumption          : 0.09
% 3.22/1.60  Abstraction          : 0.03
% 3.22/1.60  MUC search           : 0.00
% 3.22/1.60  Cooper               : 0.00
% 3.22/1.60  Total                : 0.94
% 3.22/1.60  Index Insertion      : 0.00
% 3.22/1.60  Index Deletion       : 0.00
% 3.22/1.60  Index Matching       : 0.00
% 3.22/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
