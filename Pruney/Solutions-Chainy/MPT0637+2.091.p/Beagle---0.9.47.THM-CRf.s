%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:36 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   50 (  61 expanded)
%              Number of leaves         :   28 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  78 expanded)
%              Number of equality atoms :   25 (  27 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v4_relat_1(k6_relat_1(A),A)
      & v5_relat_1(k6_relat_1(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc24_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_24] : v1_relat_1(k6_relat_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_26,plain,(
    ! [A_24] : v4_relat_1(k6_relat_1(A_24),A_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_94,plain,(
    ! [B_41,A_42] :
      ( k7_relat_1(B_41,A_42) = B_41
      | ~ v4_relat_1(B_41,A_42)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_97,plain,(
    ! [A_24] :
      ( k7_relat_1(k6_relat_1(A_24),A_24) = k6_relat_1(A_24)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_100,plain,(
    ! [A_24] : k7_relat_1(k6_relat_1(A_24),A_24) = k6_relat_1(A_24) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_97])).

tff(c_149,plain,(
    ! [C_52,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_52,A_53),B_54) = k7_relat_1(C_52,k3_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_164,plain,(
    ! [A_24,B_54] :
      ( k7_relat_1(k6_relat_1(A_24),k3_xboole_0(A_24,B_54)) = k7_relat_1(k6_relat_1(A_24),B_54)
      | ~ v1_relat_1(k6_relat_1(A_24)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_149])).

tff(c_195,plain,(
    ! [A_57,B_58] : k7_relat_1(k6_relat_1(A_57),k3_xboole_0(A_57,B_58)) = k7_relat_1(k6_relat_1(A_57),B_58) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_164])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k5_relat_1(k6_relat_1(A_22),B_23) = k7_relat_1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_19] : k2_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_110,plain,(
    ! [B_44,A_45] :
      ( k5_relat_1(B_44,k6_relat_1(A_45)) = B_44
      | ~ r1_tarski(k2_relat_1(B_44),A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_113,plain,(
    ! [A_19,A_45] :
      ( k5_relat_1(k6_relat_1(A_19),k6_relat_1(A_45)) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_45)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_125,plain,(
    ! [A_50,A_51] :
      ( k5_relat_1(k6_relat_1(A_50),k6_relat_1(A_51)) = k6_relat_1(A_50)
      | ~ r1_tarski(A_50,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_113])).

tff(c_141,plain,(
    ! [A_51,A_22] :
      ( k7_relat_1(k6_relat_1(A_51),A_22) = k6_relat_1(A_22)
      | ~ r1_tarski(A_22,A_51)
      | ~ v1_relat_1(k6_relat_1(A_51)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_125])).

tff(c_147,plain,(
    ! [A_51,A_22] :
      ( k7_relat_1(k6_relat_1(A_51),A_22) = k6_relat_1(A_22)
      | ~ r1_tarski(A_22,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_141])).

tff(c_201,plain,(
    ! [A_57,B_58] :
      ( k7_relat_1(k6_relat_1(A_57),B_58) = k6_relat_1(k3_xboole_0(A_57,B_58))
      | ~ r1_tarski(k3_xboole_0(A_57,B_58),A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_195,c_147])).

tff(c_214,plain,(
    ! [A_57,B_58] : k7_relat_1(k6_relat_1(A_57),B_58) = k6_relat_1(k3_xboole_0(A_57,B_58)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_201])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_84,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_82])).

tff(c_224,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_84])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:39:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  
% 1.87/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.19  %$ v5_relat_1 > v4_relat_1 > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.87/1.19  
% 1.87/1.19  %Foreground sorts:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Background operators:
% 1.87/1.19  
% 1.87/1.19  
% 1.87/1.19  %Foreground operators:
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.87/1.19  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.87/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.87/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.87/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.87/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.87/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.87/1.19  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.87/1.19  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.87/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.19  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 1.87/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.87/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.87/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.87/1.19  
% 1.87/1.20  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.87/1.20  tff(f_65, axiom, (![A]: ((v1_relat_1(k6_relat_1(A)) & v4_relat_1(k6_relat_1(A), A)) & v5_relat_1(k6_relat_1(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc24_relat_1)).
% 1.87/1.20  tff(f_45, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 1.87/1.20  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.87/1.20  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 1.87/1.20  tff(f_49, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.87/1.20  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_relat_1)).
% 1.87/1.20  tff(f_68, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 1.87/1.20  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.87/1.20  tff(c_24, plain, (![A_24]: (v1_relat_1(k6_relat_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.20  tff(c_26, plain, (![A_24]: (v4_relat_1(k6_relat_1(A_24), A_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.87/1.20  tff(c_94, plain, (![B_41, A_42]: (k7_relat_1(B_41, A_42)=B_41 | ~v4_relat_1(B_41, A_42) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.87/1.20  tff(c_97, plain, (![A_24]: (k7_relat_1(k6_relat_1(A_24), A_24)=k6_relat_1(A_24) | ~v1_relat_1(k6_relat_1(A_24)))), inference(resolution, [status(thm)], [c_26, c_94])).
% 1.87/1.20  tff(c_100, plain, (![A_24]: (k7_relat_1(k6_relat_1(A_24), A_24)=k6_relat_1(A_24))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_97])).
% 1.87/1.20  tff(c_149, plain, (![C_52, A_53, B_54]: (k7_relat_1(k7_relat_1(C_52, A_53), B_54)=k7_relat_1(C_52, k3_xboole_0(A_53, B_54)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.87/1.20  tff(c_164, plain, (![A_24, B_54]: (k7_relat_1(k6_relat_1(A_24), k3_xboole_0(A_24, B_54))=k7_relat_1(k6_relat_1(A_24), B_54) | ~v1_relat_1(k6_relat_1(A_24)))), inference(superposition, [status(thm), theory('equality')], [c_100, c_149])).
% 1.87/1.20  tff(c_195, plain, (![A_57, B_58]: (k7_relat_1(k6_relat_1(A_57), k3_xboole_0(A_57, B_58))=k7_relat_1(k6_relat_1(A_57), B_58))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_164])).
% 1.87/1.20  tff(c_22, plain, (![A_22, B_23]: (k5_relat_1(k6_relat_1(A_22), B_23)=k7_relat_1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.20  tff(c_18, plain, (![A_19]: (k2_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.87/1.20  tff(c_110, plain, (![B_44, A_45]: (k5_relat_1(B_44, k6_relat_1(A_45))=B_44 | ~r1_tarski(k2_relat_1(B_44), A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.87/1.20  tff(c_113, plain, (![A_19, A_45]: (k5_relat_1(k6_relat_1(A_19), k6_relat_1(A_45))=k6_relat_1(A_19) | ~r1_tarski(A_19, A_45) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_110])).
% 1.87/1.20  tff(c_125, plain, (![A_50, A_51]: (k5_relat_1(k6_relat_1(A_50), k6_relat_1(A_51))=k6_relat_1(A_50) | ~r1_tarski(A_50, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_113])).
% 1.87/1.20  tff(c_141, plain, (![A_51, A_22]: (k7_relat_1(k6_relat_1(A_51), A_22)=k6_relat_1(A_22) | ~r1_tarski(A_22, A_51) | ~v1_relat_1(k6_relat_1(A_51)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_125])).
% 1.87/1.20  tff(c_147, plain, (![A_51, A_22]: (k7_relat_1(k6_relat_1(A_51), A_22)=k6_relat_1(A_22) | ~r1_tarski(A_22, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_141])).
% 1.87/1.20  tff(c_201, plain, (![A_57, B_58]: (k7_relat_1(k6_relat_1(A_57), B_58)=k6_relat_1(k3_xboole_0(A_57, B_58)) | ~r1_tarski(k3_xboole_0(A_57, B_58), A_57))), inference(superposition, [status(thm), theory('equality')], [c_195, c_147])).
% 1.87/1.20  tff(c_214, plain, (![A_57, B_58]: (k7_relat_1(k6_relat_1(A_57), B_58)=k6_relat_1(k3_xboole_0(A_57, B_58)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_201])).
% 1.87/1.20  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.87/1.20  tff(c_82, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_22, c_30])).
% 1.87/1.20  tff(c_84, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_82])).
% 1.87/1.20  tff(c_224, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_214, c_84])).
% 1.87/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  Inference rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Ref     : 0
% 1.87/1.20  #Sup     : 40
% 1.87/1.20  #Fact    : 0
% 1.87/1.20  #Define  : 0
% 1.87/1.20  #Split   : 1
% 1.87/1.20  #Chain   : 0
% 1.87/1.20  #Close   : 0
% 1.87/1.20  
% 1.87/1.20  Ordering : KBO
% 1.87/1.20  
% 1.87/1.20  Simplification rules
% 1.87/1.20  ----------------------
% 1.87/1.20  #Subsume      : 2
% 1.87/1.20  #Demod        : 13
% 1.87/1.20  #Tautology    : 26
% 1.87/1.20  #SimpNegUnit  : 0
% 1.87/1.20  #BackRed      : 3
% 1.87/1.20  
% 1.87/1.20  #Partial instantiations: 0
% 1.87/1.20  #Strategies tried      : 1
% 1.87/1.20  
% 1.87/1.20  Timing (in seconds)
% 1.87/1.20  ----------------------
% 1.87/1.20  Preprocessing        : 0.29
% 1.87/1.20  Parsing              : 0.16
% 1.87/1.21  CNF conversion       : 0.02
% 1.87/1.21  Main loop            : 0.15
% 1.87/1.21  Inferencing          : 0.06
% 1.87/1.21  Reduction            : 0.04
% 1.87/1.21  Demodulation         : 0.03
% 1.87/1.21  BG Simplification    : 0.01
% 1.87/1.21  Subsumption          : 0.02
% 1.87/1.21  Abstraction          : 0.01
% 1.87/1.21  MUC search           : 0.00
% 1.87/1.21  Cooper               : 0.00
% 1.87/1.21  Total                : 0.46
% 1.87/1.21  Index Insertion      : 0.00
% 1.87/1.21  Index Deletion       : 0.00
% 1.87/1.21  Index Matching       : 0.00
% 1.87/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
