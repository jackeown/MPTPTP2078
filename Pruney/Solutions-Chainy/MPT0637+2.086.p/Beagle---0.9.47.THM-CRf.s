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
% DateTime   : Thu Dec  3 10:03:35 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 (  60 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_56,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_12,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_67,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_76,plain,(
    ! [A_34,B_35] : r1_tarski(k3_xboole_0(A_34,B_35),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_2])).

tff(c_20,plain,(
    ! [A_20] : k1_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_191,plain,(
    ! [B_55,A_56] :
      ( k7_relat_1(B_55,k3_xboole_0(k1_relat_1(B_55),A_56)) = k7_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_22,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_140,plain,(
    ! [B_47,A_48] :
      ( k5_relat_1(B_47,k6_relat_1(A_48)) = B_47
      | ~ r1_tarski(k2_relat_1(B_47),A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_143,plain,(
    ! [A_20,A_48] :
      ( k5_relat_1(k6_relat_1(A_20),k6_relat_1(A_48)) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_48)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_140])).

tff(c_155,plain,(
    ! [A_51,A_52] :
      ( k5_relat_1(k6_relat_1(A_51),k6_relat_1(A_52)) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_143])).

tff(c_26,plain,(
    ! [A_23,B_24] :
      ( k5_relat_1(k6_relat_1(A_23),B_24) = k7_relat_1(B_24,A_23)
      | ~ v1_relat_1(B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_161,plain,(
    ! [A_52,A_51] :
      ( k7_relat_1(k6_relat_1(A_52),A_51) = k6_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_52))
      | ~ r1_tarski(A_51,A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_26])).

tff(c_174,plain,(
    ! [A_52,A_51] :
      ( k7_relat_1(k6_relat_1(A_52),A_51) = k6_relat_1(A_51)
      | ~ r1_tarski(A_51,A_52) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_161])).

tff(c_198,plain,(
    ! [A_52,A_56] :
      ( k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_52)),A_56)) = k7_relat_1(k6_relat_1(A_52),A_56)
      | ~ r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_52)),A_56),A_52)
      | ~ v1_relat_1(k6_relat_1(A_52)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_174])).

tff(c_211,plain,(
    ! [A_52,A_56] : k7_relat_1(k6_relat_1(A_52),A_56) = k6_relat_1(k3_xboole_0(A_52,A_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_76,c_20,c_20,c_198])).

tff(c_86,plain,(
    ! [A_38,B_39] :
      ( k5_relat_1(k6_relat_1(A_38),B_39) = k7_relat_1(B_39,A_38)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_28,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_92,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_28])).

tff(c_98,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_92])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:13:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.20  
% 1.95/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.21  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.95/1.21  
% 1.95/1.21  %Foreground sorts:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Background operators:
% 1.95/1.21  
% 1.95/1.21  
% 1.95/1.21  %Foreground operators:
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.21  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.95/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.95/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.95/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.95/1.21  
% 1.95/1.22  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.95/1.22  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.95/1.22  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.95/1.22  tff(f_56, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.95/1.22  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 1.95/1.22  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.95/1.22  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.95/1.22  tff(f_69, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.95/1.22  tff(c_12, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.95/1.22  tff(c_67, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.22  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.95/1.22  tff(c_76, plain, (![A_34, B_35]: (r1_tarski(k3_xboole_0(A_34, B_35), A_34))), inference(superposition, [status(thm), theory('equality')], [c_67, c_2])).
% 1.95/1.22  tff(c_20, plain, (![A_20]: (k1_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.22  tff(c_191, plain, (![B_55, A_56]: (k7_relat_1(B_55, k3_xboole_0(k1_relat_1(B_55), A_56))=k7_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.22  tff(c_22, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.22  tff(c_140, plain, (![B_47, A_48]: (k5_relat_1(B_47, k6_relat_1(A_48))=B_47 | ~r1_tarski(k2_relat_1(B_47), A_48) | ~v1_relat_1(B_47))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.22  tff(c_143, plain, (![A_20, A_48]: (k5_relat_1(k6_relat_1(A_20), k6_relat_1(A_48))=k6_relat_1(A_20) | ~r1_tarski(A_20, A_48) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_140])).
% 1.95/1.22  tff(c_155, plain, (![A_51, A_52]: (k5_relat_1(k6_relat_1(A_51), k6_relat_1(A_52))=k6_relat_1(A_51) | ~r1_tarski(A_51, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_143])).
% 1.95/1.22  tff(c_26, plain, (![A_23, B_24]: (k5_relat_1(k6_relat_1(A_23), B_24)=k7_relat_1(B_24, A_23) | ~v1_relat_1(B_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.22  tff(c_161, plain, (![A_52, A_51]: (k7_relat_1(k6_relat_1(A_52), A_51)=k6_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_52)) | ~r1_tarski(A_51, A_52))), inference(superposition, [status(thm), theory('equality')], [c_155, c_26])).
% 1.95/1.22  tff(c_174, plain, (![A_52, A_51]: (k7_relat_1(k6_relat_1(A_52), A_51)=k6_relat_1(A_51) | ~r1_tarski(A_51, A_52))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_161])).
% 1.95/1.22  tff(c_198, plain, (![A_52, A_56]: (k6_relat_1(k3_xboole_0(k1_relat_1(k6_relat_1(A_52)), A_56))=k7_relat_1(k6_relat_1(A_52), A_56) | ~r1_tarski(k3_xboole_0(k1_relat_1(k6_relat_1(A_52)), A_56), A_52) | ~v1_relat_1(k6_relat_1(A_52)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_174])).
% 1.95/1.22  tff(c_211, plain, (![A_52, A_56]: (k7_relat_1(k6_relat_1(A_52), A_56)=k6_relat_1(k3_xboole_0(A_52, A_56)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_76, c_20, c_20, c_198])).
% 1.95/1.22  tff(c_86, plain, (![A_38, B_39]: (k5_relat_1(k6_relat_1(A_38), B_39)=k7_relat_1(B_39, A_38) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.95/1.22  tff(c_28, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.22  tff(c_92, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_86, c_28])).
% 1.95/1.22  tff(c_98, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_92])).
% 1.95/1.22  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_211, c_98])).
% 1.95/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.22  
% 1.95/1.22  Inference rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Ref     : 0
% 1.95/1.22  #Sup     : 41
% 1.95/1.22  #Fact    : 0
% 1.95/1.22  #Define  : 0
% 1.95/1.22  #Split   : 1
% 1.95/1.22  #Chain   : 0
% 1.95/1.22  #Close   : 0
% 1.95/1.22  
% 1.95/1.22  Ordering : KBO
% 1.95/1.22  
% 1.95/1.22  Simplification rules
% 1.95/1.22  ----------------------
% 1.95/1.22  #Subsume      : 2
% 1.95/1.22  #Demod        : 18
% 1.95/1.22  #Tautology    : 28
% 1.95/1.22  #SimpNegUnit  : 0
% 1.95/1.22  #BackRed      : 2
% 1.95/1.22  
% 1.95/1.22  #Partial instantiations: 0
% 1.95/1.22  #Strategies tried      : 1
% 1.95/1.22  
% 1.95/1.22  Timing (in seconds)
% 1.95/1.22  ----------------------
% 1.95/1.22  Preprocessing        : 0.29
% 1.95/1.22  Parsing              : 0.16
% 1.95/1.22  CNF conversion       : 0.02
% 1.95/1.22  Main loop            : 0.15
% 1.95/1.22  Inferencing          : 0.06
% 1.95/1.22  Reduction            : 0.05
% 1.95/1.22  Demodulation         : 0.04
% 1.95/1.22  BG Simplification    : 0.01
% 1.95/1.22  Subsumption          : 0.02
% 1.95/1.22  Abstraction          : 0.01
% 1.95/1.22  MUC search           : 0.00
% 1.95/1.22  Cooper               : 0.00
% 1.95/1.22  Total                : 0.47
% 1.95/1.22  Index Insertion      : 0.00
% 1.95/1.22  Index Deletion       : 0.00
% 1.95/1.22  Index Matching       : 0.00
% 1.95/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
