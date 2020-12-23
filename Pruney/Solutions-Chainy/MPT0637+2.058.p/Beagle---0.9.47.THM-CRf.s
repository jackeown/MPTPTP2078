%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 3.51s
% Output     : CNFRefutation 3.51s
% Verified   : 
% Statistics : Number of formulae       :   47 (  62 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   53 (  72 expanded)
%              Number of equality atoms :   26 (  32 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_64,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_84,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_80,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : v1_relat_1(k6_relat_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_20,plain,(
    ! [A_23] : k2_relat_1(k6_relat_1(A_23)) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_126,plain,(
    ! [A_48,B_49] :
      ( k5_relat_1(k6_relat_1(A_48),B_49) = k7_relat_1(B_49,A_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_28,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k6_relat_1(k2_relat_1(A_29))) = A_29
      | ~ v1_relat_1(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_133,plain,(
    ! [A_48] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_48))),A_48) = k6_relat_1(A_48)
      | ~ v1_relat_1(k6_relat_1(A_48))
      | ~ v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_48)))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_28])).

tff(c_163,plain,(
    ! [A_48] : k7_relat_1(k6_relat_1(A_48),A_48) = k6_relat_1(A_48) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_10,c_20,c_133])).

tff(c_570,plain,(
    ! [C_77,A_78,B_79] :
      ( k7_relat_1(k7_relat_1(C_77,A_78),B_79) = k7_relat_1(C_77,k3_xboole_0(A_78,B_79))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_609,plain,(
    ! [A_48,B_79] :
      ( k7_relat_1(k6_relat_1(A_48),k3_xboole_0(A_48,B_79)) = k7_relat_1(k6_relat_1(A_48),B_79)
      | ~ v1_relat_1(k6_relat_1(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_570])).

tff(c_1238,plain,(
    ! [A_109,B_110] : k7_relat_1(k6_relat_1(A_109),k3_xboole_0(A_109,B_110)) = k7_relat_1(k6_relat_1(A_109),B_110) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_609])).

tff(c_290,plain,(
    ! [B_62,A_63] :
      ( k5_relat_1(B_62,k6_relat_1(A_63)) = B_62
      | ~ r1_tarski(k2_relat_1(B_62),A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_297,plain,(
    ! [A_23,A_63] :
      ( k5_relat_1(k6_relat_1(A_23),k6_relat_1(A_63)) = k6_relat_1(A_23)
      | ~ r1_tarski(A_23,A_63)
      | ~ v1_relat_1(k6_relat_1(A_23)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_290])).

tff(c_671,plain,(
    ! [A_83,A_84] :
      ( k5_relat_1(k6_relat_1(A_83),k6_relat_1(A_84)) = k6_relat_1(A_83)
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_297])).

tff(c_32,plain,(
    ! [A_32,B_33] :
      ( k5_relat_1(k6_relat_1(A_32),B_33) = k7_relat_1(B_33,A_32)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_683,plain,(
    ! [A_84,A_83] :
      ( k7_relat_1(k6_relat_1(A_84),A_83) = k6_relat_1(A_83)
      | ~ v1_relat_1(k6_relat_1(A_84))
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_671,c_32])).

tff(c_727,plain,(
    ! [A_84,A_83] :
      ( k7_relat_1(k6_relat_1(A_84),A_83) = k6_relat_1(A_83)
      | ~ r1_tarski(A_83,A_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_683])).

tff(c_1247,plain,(
    ! [A_109,B_110] :
      ( k7_relat_1(k6_relat_1(A_109),B_110) = k6_relat_1(k3_xboole_0(A_109,B_110))
      | ~ r1_tarski(k3_xboole_0(A_109,B_110),A_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_727])).

tff(c_1290,plain,(
    ! [A_109,B_110] : k7_relat_1(k6_relat_1(A_109),B_110) = k6_relat_1(k3_xboole_0(A_109,B_110)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1247])).

tff(c_34,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_136,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_34])).

tff(c_165,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_136])).

tff(c_1332,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1290,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:34:12 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.51/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.95  
% 3.51/1.95  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.95  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.51/1.95  
% 3.51/1.95  %Foreground sorts:
% 3.51/1.95  
% 3.51/1.95  
% 3.51/1.95  %Background operators:
% 3.51/1.95  
% 3.51/1.95  
% 3.51/1.95  %Foreground operators:
% 3.51/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.51/1.95  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.51/1.95  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.51/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.51/1.95  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.51/1.95  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.51/1.95  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.51/1.95  tff('#skF_2', type, '#skF_2': $i).
% 3.51/1.95  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.51/1.95  tff('#skF_1', type, '#skF_1': $i).
% 3.51/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.51/1.95  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.51/1.95  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.51/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.51/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.51/1.95  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.51/1.95  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.51/1.95  
% 3.51/1.96  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.51/1.96  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.51/1.96  tff(f_64, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.51/1.96  tff(f_92, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 3.51/1.96  tff(f_84, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_relat_1)).
% 3.51/1.96  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 3.51/1.96  tff(f_80, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 3.51/1.96  tff(f_95, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.51/1.96  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.51/1.96  tff(c_10, plain, (![A_9]: (v1_relat_1(k6_relat_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.51/1.96  tff(c_20, plain, (![A_23]: (k2_relat_1(k6_relat_1(A_23))=A_23)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.51/1.96  tff(c_126, plain, (![A_48, B_49]: (k5_relat_1(k6_relat_1(A_48), B_49)=k7_relat_1(B_49, A_48) | ~v1_relat_1(B_49))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.51/1.96  tff(c_28, plain, (![A_29]: (k5_relat_1(A_29, k6_relat_1(k2_relat_1(A_29)))=A_29 | ~v1_relat_1(A_29))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.51/1.96  tff(c_133, plain, (![A_48]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_48))), A_48)=k6_relat_1(A_48) | ~v1_relat_1(k6_relat_1(A_48)) | ~v1_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_48)))))), inference(superposition, [status(thm), theory('equality')], [c_126, c_28])).
% 3.51/1.96  tff(c_163, plain, (![A_48]: (k7_relat_1(k6_relat_1(A_48), A_48)=k6_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_10, c_20, c_133])).
% 3.51/1.96  tff(c_570, plain, (![C_77, A_78, B_79]: (k7_relat_1(k7_relat_1(C_77, A_78), B_79)=k7_relat_1(C_77, k3_xboole_0(A_78, B_79)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.51/1.96  tff(c_609, plain, (![A_48, B_79]: (k7_relat_1(k6_relat_1(A_48), k3_xboole_0(A_48, B_79))=k7_relat_1(k6_relat_1(A_48), B_79) | ~v1_relat_1(k6_relat_1(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_163, c_570])).
% 3.51/1.96  tff(c_1238, plain, (![A_109, B_110]: (k7_relat_1(k6_relat_1(A_109), k3_xboole_0(A_109, B_110))=k7_relat_1(k6_relat_1(A_109), B_110))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_609])).
% 3.51/1.96  tff(c_290, plain, (![B_62, A_63]: (k5_relat_1(B_62, k6_relat_1(A_63))=B_62 | ~r1_tarski(k2_relat_1(B_62), A_63) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.51/1.96  tff(c_297, plain, (![A_23, A_63]: (k5_relat_1(k6_relat_1(A_23), k6_relat_1(A_63))=k6_relat_1(A_23) | ~r1_tarski(A_23, A_63) | ~v1_relat_1(k6_relat_1(A_23)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_290])).
% 3.51/1.96  tff(c_671, plain, (![A_83, A_84]: (k5_relat_1(k6_relat_1(A_83), k6_relat_1(A_84))=k6_relat_1(A_83) | ~r1_tarski(A_83, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_297])).
% 3.51/1.96  tff(c_32, plain, (![A_32, B_33]: (k5_relat_1(k6_relat_1(A_32), B_33)=k7_relat_1(B_33, A_32) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.51/1.96  tff(c_683, plain, (![A_84, A_83]: (k7_relat_1(k6_relat_1(A_84), A_83)=k6_relat_1(A_83) | ~v1_relat_1(k6_relat_1(A_84)) | ~r1_tarski(A_83, A_84))), inference(superposition, [status(thm), theory('equality')], [c_671, c_32])).
% 3.51/1.96  tff(c_727, plain, (![A_84, A_83]: (k7_relat_1(k6_relat_1(A_84), A_83)=k6_relat_1(A_83) | ~r1_tarski(A_83, A_84))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_683])).
% 3.51/1.96  tff(c_1247, plain, (![A_109, B_110]: (k7_relat_1(k6_relat_1(A_109), B_110)=k6_relat_1(k3_xboole_0(A_109, B_110)) | ~r1_tarski(k3_xboole_0(A_109, B_110), A_109))), inference(superposition, [status(thm), theory('equality')], [c_1238, c_727])).
% 3.51/1.96  tff(c_1290, plain, (![A_109, B_110]: (k7_relat_1(k6_relat_1(A_109), B_110)=k6_relat_1(k3_xboole_0(A_109, B_110)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1247])).
% 3.51/1.96  tff(c_34, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.51/1.96  tff(c_136, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_126, c_34])).
% 3.51/1.96  tff(c_165, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_136])).
% 3.51/1.96  tff(c_1332, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1290, c_165])).
% 3.51/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.51/1.96  
% 3.51/1.96  Inference rules
% 3.51/1.96  ----------------------
% 3.51/1.96  #Ref     : 0
% 3.51/1.96  #Sup     : 278
% 3.51/1.96  #Fact    : 0
% 3.51/1.96  #Define  : 0
% 3.51/1.96  #Split   : 2
% 3.51/1.96  #Chain   : 0
% 3.51/1.96  #Close   : 0
% 3.51/1.96  
% 3.51/1.96  Ordering : KBO
% 3.51/1.96  
% 3.51/1.96  Simplification rules
% 3.51/1.96  ----------------------
% 3.51/1.96  #Subsume      : 15
% 3.51/1.96  #Demod        : 299
% 3.51/1.96  #Tautology    : 153
% 3.51/1.96  #SimpNegUnit  : 0
% 3.51/1.96  #BackRed      : 6
% 3.51/1.96  
% 3.51/1.96  #Partial instantiations: 0
% 3.51/1.96  #Strategies tried      : 1
% 3.51/1.96  
% 3.51/1.96  Timing (in seconds)
% 3.51/1.96  ----------------------
% 3.51/1.97  Preprocessing        : 0.49
% 3.51/1.97  Parsing              : 0.26
% 3.51/1.97  CNF conversion       : 0.03
% 3.51/1.97  Main loop            : 0.57
% 3.51/1.97  Inferencing          : 0.22
% 3.51/1.97  Reduction            : 0.19
% 3.51/1.97  Demodulation         : 0.14
% 3.51/1.97  BG Simplification    : 0.04
% 3.51/1.97  Subsumption          : 0.08
% 3.51/1.97  Abstraction          : 0.04
% 3.51/1.97  MUC search           : 0.00
% 3.51/1.97  Cooper               : 0.00
% 3.51/1.97  Total                : 1.11
% 3.51/1.97  Index Insertion      : 0.00
% 3.51/1.97  Index Deletion       : 0.00
% 3.51/1.97  Index Matching       : 0.00
% 3.51/1.97  BG Taut test         : 0.00
%------------------------------------------------------------------------------
