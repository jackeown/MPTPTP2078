%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.52s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 (  64 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_30,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_16,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_237,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ r1_tarski(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_251,plain,(
    ! [A_16,A_51] :
      ( k7_relat_1(k6_relat_1(A_16),A_51) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_51)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_237])).

tff(c_256,plain,(
    ! [A_16,A_51] :
      ( k7_relat_1(k6_relat_1(A_16),A_51) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_251])).

tff(c_303,plain,(
    ! [B_54,A_55] :
      ( k3_xboole_0(k1_relat_1(B_54),A_55) = k1_relat_1(k7_relat_1(B_54,A_55))
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_326,plain,(
    ! [A_16,A_55] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_16),A_55)) = k3_xboole_0(A_16,A_55)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_303])).

tff(c_378,plain,(
    ! [A_59,A_60] : k1_relat_1(k7_relat_1(k6_relat_1(A_59),A_60)) = k3_xboole_0(A_59,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_326])).

tff(c_399,plain,(
    ! [A_16,A_51] :
      ( k3_xboole_0(A_16,A_51) = k1_relat_1(k6_relat_1(A_16))
      | ~ r1_tarski(A_16,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_378])).

tff(c_476,plain,(
    ! [A_66,A_67] :
      ( k3_xboole_0(A_66,A_67) = A_66
      | ~ r1_tarski(A_66,A_67) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_399])).

tff(c_502,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_476])).

tff(c_32,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [A_35,B_36] : k1_setfam_1(k2_tarski(A_35,B_36)) = k3_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_141,plain,(
    ! [B_37,A_38] : k1_setfam_1(k2_tarski(B_37,A_38)) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_126])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_147,plain,(
    ! [B_37,A_38] : k3_xboole_0(B_37,A_38) = k3_xboole_0(A_38,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_8])).

tff(c_331,plain,(
    ! [C_56,A_57,B_58] :
      ( k7_relat_1(k7_relat_1(C_56,A_57),B_58) = k7_relat_1(C_56,k3_xboole_0(A_57,B_58))
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_28,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_343,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_28])).

tff(c_372,plain,(
    k7_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k7_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_147,c_343])).

tff(c_505,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_372])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:26:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.36  
% 2.24/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.36  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.24/1.36  
% 2.24/1.36  %Foreground sorts:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Background operators:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Foreground operators:
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.36  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.24/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.36  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.24/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.24/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.24/1.36  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.36  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.24/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.24/1.36  
% 2.52/1.38  tff(f_76, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.52/1.38  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.52/1.38  tff(f_39, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.52/1.38  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.52/1.38  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.52/1.38  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.52/1.38  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.52/1.38  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.52/1.38  tff(c_30, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.38  tff(c_16, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.52/1.38  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.52/1.38  tff(c_237, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~r1_tarski(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.52/1.38  tff(c_251, plain, (![A_16, A_51]: (k7_relat_1(k6_relat_1(A_16), A_51)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_51) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_237])).
% 2.52/1.38  tff(c_256, plain, (![A_16, A_51]: (k7_relat_1(k6_relat_1(A_16), A_51)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_251])).
% 2.52/1.38  tff(c_303, plain, (![B_54, A_55]: (k3_xboole_0(k1_relat_1(B_54), A_55)=k1_relat_1(k7_relat_1(B_54, A_55)) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.52/1.38  tff(c_326, plain, (![A_16, A_55]: (k1_relat_1(k7_relat_1(k6_relat_1(A_16), A_55))=k3_xboole_0(A_16, A_55) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_303])).
% 2.52/1.38  tff(c_378, plain, (![A_59, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_59), A_60))=k3_xboole_0(A_59, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_326])).
% 2.52/1.38  tff(c_399, plain, (![A_16, A_51]: (k3_xboole_0(A_16, A_51)=k1_relat_1(k6_relat_1(A_16)) | ~r1_tarski(A_16, A_51))), inference(superposition, [status(thm), theory('equality')], [c_256, c_378])).
% 2.52/1.38  tff(c_476, plain, (![A_66, A_67]: (k3_xboole_0(A_66, A_67)=A_66 | ~r1_tarski(A_66, A_67))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_399])).
% 2.52/1.38  tff(c_502, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_30, c_476])).
% 2.52/1.38  tff(c_32, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.38  tff(c_4, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.52/1.38  tff(c_126, plain, (![A_35, B_36]: (k1_setfam_1(k2_tarski(A_35, B_36))=k3_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.38  tff(c_141, plain, (![B_37, A_38]: (k1_setfam_1(k2_tarski(B_37, A_38))=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_4, c_126])).
% 2.52/1.38  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.52/1.38  tff(c_147, plain, (![B_37, A_38]: (k3_xboole_0(B_37, A_38)=k3_xboole_0(A_38, B_37))), inference(superposition, [status(thm), theory('equality')], [c_141, c_8])).
% 2.52/1.38  tff(c_331, plain, (![C_56, A_57, B_58]: (k7_relat_1(k7_relat_1(C_56, A_57), B_58)=k7_relat_1(C_56, k3_xboole_0(A_57, B_58)) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.52/1.38  tff(c_28, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.52/1.38  tff(c_343, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_331, c_28])).
% 2.52/1.38  tff(c_372, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k7_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_147, c_343])).
% 2.52/1.38  tff(c_505, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_502, c_372])).
% 2.52/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.52/1.38  
% 2.52/1.38  Inference rules
% 2.52/1.38  ----------------------
% 2.52/1.38  #Ref     : 0
% 2.52/1.38  #Sup     : 111
% 2.52/1.38  #Fact    : 0
% 2.52/1.38  #Define  : 0
% 2.52/1.38  #Split   : 0
% 2.52/1.38  #Chain   : 0
% 2.52/1.38  #Close   : 0
% 2.52/1.38  
% 2.52/1.38  Ordering : KBO
% 2.52/1.38  
% 2.52/1.38  Simplification rules
% 2.52/1.38  ----------------------
% 2.52/1.38  #Subsume      : 6
% 2.52/1.38  #Demod        : 43
% 2.52/1.38  #Tautology    : 61
% 2.52/1.38  #SimpNegUnit  : 0
% 2.52/1.38  #BackRed      : 1
% 2.52/1.38  
% 2.52/1.38  #Partial instantiations: 0
% 2.52/1.38  #Strategies tried      : 1
% 2.52/1.38  
% 2.52/1.38  Timing (in seconds)
% 2.52/1.38  ----------------------
% 2.52/1.38  Preprocessing        : 0.32
% 2.52/1.38  Parsing              : 0.18
% 2.52/1.38  CNF conversion       : 0.02
% 2.52/1.38  Main loop            : 0.23
% 2.52/1.38  Inferencing          : 0.08
% 2.52/1.38  Reduction            : 0.08
% 2.52/1.38  Demodulation         : 0.06
% 2.52/1.38  BG Simplification    : 0.02
% 2.52/1.38  Subsumption          : 0.04
% 2.52/1.38  Abstraction          : 0.02
% 2.52/1.38  MUC search           : 0.00
% 2.52/1.38  Cooper               : 0.00
% 2.52/1.38  Total                : 0.58
% 2.52/1.38  Index Insertion      : 0.00
% 2.52/1.38  Index Deletion       : 0.00
% 2.52/1.38  Index Matching       : 0.00
% 2.52/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
