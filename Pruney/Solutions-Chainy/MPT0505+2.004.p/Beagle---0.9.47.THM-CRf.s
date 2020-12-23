%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:51 EST 2020

% Result     : Theorem 2.41s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   50 (  59 expanded)
%              Number of leaves         :   27 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   49 (  64 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_42,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_40,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_21] : k1_relat_1(k6_relat_1(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    ! [A_15] : v1_relat_1(k6_relat_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_229,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ r1_tarski(k1_relat_1(B_58),A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_236,plain,(
    ! [A_21,A_59] :
      ( k7_relat_1(k6_relat_1(A_21),A_59) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_59)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_239,plain,(
    ! [A_21,A_59] :
      ( k7_relat_1(k6_relat_1(A_21),A_59) = k6_relat_1(A_21)
      | ~ r1_tarski(A_21,A_59) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_236])).

tff(c_281,plain,(
    ! [B_62,A_63] :
      ( k3_xboole_0(k1_relat_1(B_62),A_63) = k1_relat_1(k7_relat_1(B_62,A_63))
      | ~ v1_relat_1(B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_304,plain,(
    ! [A_21,A_63] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_21),A_63)) = k3_xboole_0(A_21,A_63)
      | ~ v1_relat_1(k6_relat_1(A_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_281])).

tff(c_309,plain,(
    ! [A_64,A_65] : k1_relat_1(k7_relat_1(k6_relat_1(A_64),A_65)) = k3_xboole_0(A_64,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_304])).

tff(c_327,plain,(
    ! [A_21,A_59] :
      ( k3_xboole_0(A_21,A_59) = k1_relat_1(k6_relat_1(A_21))
      | ~ r1_tarski(A_21,A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_309])).

tff(c_383,plain,(
    ! [A_70,A_71] :
      ( k3_xboole_0(A_70,A_71) = A_70
      | ~ r1_tarski(A_70,A_71) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_327])).

tff(c_392,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_383])).

tff(c_8,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_105,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_151,plain,(
    ! [A_43,B_44] : k1_setfam_1(k2_tarski(A_43,B_44)) = k3_xboole_0(B_44,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_14,plain,(
    ! [A_13,B_14] : k1_setfam_1(k2_tarski(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_157,plain,(
    ! [B_44,A_43] : k3_xboole_0(B_44,A_43) = k3_xboole_0(A_43,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_14])).

tff(c_396,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_392,c_157])).

tff(c_440,plain,(
    ! [C_75,A_76,B_77] :
      ( k7_relat_1(k7_relat_1(C_75,A_76),B_77) = k7_relat_1(C_75,k3_xboole_0(A_76,B_77))
      | ~ v1_relat_1(C_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_38,plain,(
    k7_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2') != k7_relat_1('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_456,plain,
    ( k7_relat_1('#skF_4',k3_xboole_0('#skF_3','#skF_2')) != k7_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_440,c_38])).

tff(c_482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_396,c_456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.41/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.58  
% 2.41/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.59  %$ r2_hidden > r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.41/1.59  
% 2.41/1.59  %Foreground sorts:
% 2.41/1.59  
% 2.41/1.59  
% 2.41/1.59  %Background operators:
% 2.41/1.59  
% 2.41/1.59  
% 2.41/1.59  %Foreground operators:
% 2.41/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.41/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.41/1.59  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.41/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.41/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.41/1.59  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.41/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.41/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.41/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.41/1.59  tff('#skF_3', type, '#skF_3': $i).
% 2.41/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.41/1.59  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.41/1.59  tff('#skF_4', type, '#skF_4': $i).
% 2.41/1.59  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.41/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.41/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.41/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.41/1.59  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.41/1.59  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.41/1.59  
% 2.41/1.60  tff(f_83, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.41/1.60  tff(f_54, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.41/1.60  tff(f_42, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.41/1.60  tff(f_72, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.41/1.60  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.41/1.60  tff(f_34, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.41/1.60  tff(f_40, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.41/1.60  tff(f_50, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.41/1.60  tff(c_42, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.60  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.60  tff(c_22, plain, (![A_21]: (k1_relat_1(k6_relat_1(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.41/1.60  tff(c_16, plain, (![A_15]: (v1_relat_1(k6_relat_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.41/1.60  tff(c_229, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~r1_tarski(k1_relat_1(B_58), A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.41/1.60  tff(c_236, plain, (![A_21, A_59]: (k7_relat_1(k6_relat_1(A_21), A_59)=k6_relat_1(A_21) | ~r1_tarski(A_21, A_59) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_229])).
% 2.41/1.60  tff(c_239, plain, (![A_21, A_59]: (k7_relat_1(k6_relat_1(A_21), A_59)=k6_relat_1(A_21) | ~r1_tarski(A_21, A_59))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_236])).
% 2.41/1.60  tff(c_281, plain, (![B_62, A_63]: (k3_xboole_0(k1_relat_1(B_62), A_63)=k1_relat_1(k7_relat_1(B_62, A_63)) | ~v1_relat_1(B_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.41/1.60  tff(c_304, plain, (![A_21, A_63]: (k1_relat_1(k7_relat_1(k6_relat_1(A_21), A_63))=k3_xboole_0(A_21, A_63) | ~v1_relat_1(k6_relat_1(A_21)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_281])).
% 2.41/1.60  tff(c_309, plain, (![A_64, A_65]: (k1_relat_1(k7_relat_1(k6_relat_1(A_64), A_65))=k3_xboole_0(A_64, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_304])).
% 2.41/1.60  tff(c_327, plain, (![A_21, A_59]: (k3_xboole_0(A_21, A_59)=k1_relat_1(k6_relat_1(A_21)) | ~r1_tarski(A_21, A_59))), inference(superposition, [status(thm), theory('equality')], [c_239, c_309])).
% 2.41/1.60  tff(c_383, plain, (![A_70, A_71]: (k3_xboole_0(A_70, A_71)=A_70 | ~r1_tarski(A_70, A_71))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_327])).
% 2.41/1.60  tff(c_392, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_383])).
% 2.41/1.60  tff(c_8, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.41/1.60  tff(c_105, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.60  tff(c_151, plain, (![A_43, B_44]: (k1_setfam_1(k2_tarski(A_43, B_44))=k3_xboole_0(B_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.41/1.60  tff(c_14, plain, (![A_13, B_14]: (k1_setfam_1(k2_tarski(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.41/1.60  tff(c_157, plain, (![B_44, A_43]: (k3_xboole_0(B_44, A_43)=k3_xboole_0(A_43, B_44))), inference(superposition, [status(thm), theory('equality')], [c_151, c_14])).
% 2.41/1.60  tff(c_396, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_392, c_157])).
% 2.41/1.60  tff(c_440, plain, (![C_75, A_76, B_77]: (k7_relat_1(k7_relat_1(C_75, A_76), B_77)=k7_relat_1(C_75, k3_xboole_0(A_76, B_77)) | ~v1_relat_1(C_75))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.41/1.60  tff(c_38, plain, (k7_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2')!=k7_relat_1('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.41/1.60  tff(c_456, plain, (k7_relat_1('#skF_4', k3_xboole_0('#skF_3', '#skF_2'))!=k7_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_440, c_38])).
% 2.41/1.60  tff(c_482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_396, c_456])).
% 2.41/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.41/1.60  
% 2.41/1.60  Inference rules
% 2.41/1.60  ----------------------
% 2.41/1.60  #Ref     : 0
% 2.41/1.60  #Sup     : 105
% 2.41/1.60  #Fact    : 0
% 2.41/1.60  #Define  : 0
% 2.41/1.60  #Split   : 0
% 2.41/1.60  #Chain   : 0
% 2.41/1.60  #Close   : 0
% 2.41/1.60  
% 2.41/1.60  Ordering : KBO
% 2.41/1.60  
% 2.41/1.60  Simplification rules
% 2.41/1.60  ----------------------
% 2.41/1.60  #Subsume      : 4
% 2.41/1.60  #Demod        : 35
% 2.41/1.60  #Tautology    : 64
% 2.41/1.60  #SimpNegUnit  : 0
% 2.41/1.60  #BackRed      : 0
% 2.41/1.60  
% 2.41/1.60  #Partial instantiations: 0
% 2.41/1.60  #Strategies tried      : 1
% 2.41/1.60  
% 2.41/1.60  Timing (in seconds)
% 2.41/1.60  ----------------------
% 2.41/1.60  Preprocessing        : 0.47
% 2.41/1.60  Parsing              : 0.26
% 2.41/1.60  CNF conversion       : 0.03
% 2.41/1.60  Main loop            : 0.25
% 2.41/1.60  Inferencing          : 0.10
% 2.41/1.60  Reduction            : 0.08
% 2.41/1.60  Demodulation         : 0.06
% 2.41/1.60  BG Simplification    : 0.02
% 2.41/1.60  Subsumption          : 0.04
% 2.41/1.60  Abstraction          : 0.02
% 2.41/1.60  MUC search           : 0.00
% 2.41/1.60  Cooper               : 0.00
% 2.41/1.60  Total                : 0.75
% 2.41/1.60  Index Insertion      : 0.00
% 2.41/1.60  Index Deletion       : 0.00
% 2.41/1.60  Index Matching       : 0.00
% 2.41/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
