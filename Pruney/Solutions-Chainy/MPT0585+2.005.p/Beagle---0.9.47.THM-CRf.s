%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   21 (  33 expanded)
%              Depth                    :   11
%              Number of atoms          :   62 (  99 expanded)
%              Number of equality atoms :   28 (  46 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k7_relat_1(A,k1_relat_1(B)) = k7_relat_1(A,k1_relat_1(k7_relat_1(B,k1_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t189_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_relat_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_74,plain,(
    ! [A_23,B_24] : k1_setfam_1(k2_tarski(A_23,B_24)) = k3_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_118,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_74])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_124,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_8])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k7_relat_1(B_13,A_12),B_13)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_97,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(k7_relat_1(B_13,A_12),B_13) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(resolution,[status(thm)],[c_12,c_93])).

tff(c_198,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(B_13,k7_relat_1(B_13,A_12)) = k7_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_97])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_16] :
      ( k7_relat_1(A_16,k1_relat_1(A_16)) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_219,plain,(
    ! [C_39,A_40,B_41] :
      ( k3_xboole_0(k7_relat_1(C_39,A_40),k7_relat_1(C_39,B_41)) = k7_relat_1(C_39,k3_xboole_0(A_40,B_41))
      | ~ v1_relat_1(C_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_303,plain,(
    ! [A_45,B_46] :
      ( k7_relat_1(A_45,k3_xboole_0(k1_relat_1(A_45),B_46)) = k3_xboole_0(A_45,k7_relat_1(A_45,B_46))
      | ~ v1_relat_1(A_45)
      | ~ v1_relat_1(A_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_219])).

tff(c_846,plain,(
    ! [B_63,A_64] :
      ( k7_relat_1(B_63,k1_relat_1(k7_relat_1(B_63,A_64))) = k3_xboole_0(B_63,k7_relat_1(B_63,A_64))
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_303])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_174,plain,(
    ! [B_35,A_36] :
      ( k3_xboole_0(k1_relat_1(B_35),A_36) = k1_relat_1(k7_relat_1(B_35,A_36))
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_247,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,k1_relat_1(B_43)) = k1_relat_1(k7_relat_1(B_43,A_42))
      | ~ v1_relat_1(B_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_124])).

tff(c_594,plain,(
    ! [B_59,B_58] :
      ( k1_relat_1(k7_relat_1(B_59,k1_relat_1(B_58))) = k1_relat_1(k7_relat_1(B_58,k1_relat_1(B_59)))
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_14])).

tff(c_18,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_651,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_18])).

tff(c_690,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_22,c_651])).

tff(c_855,plain,
    ( k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_846,c_690])).

tff(c_912,plain,(
    k3_xboole_0('#skF_1',k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_22,c_855])).

tff(c_916,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_912])).

tff(c_920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_916])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n023.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 18:55:35 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.51  
% 2.80/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.51  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.80/1.51  
% 2.80/1.51  %Foreground sorts:
% 2.80/1.51  
% 2.80/1.51  
% 2.80/1.51  %Background operators:
% 2.80/1.51  
% 2.80/1.51  
% 2.80/1.51  %Foreground operators:
% 2.80/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.80/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.51  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.51  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.80/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.80/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.80/1.51  
% 2.80/1.52  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.80/1.52  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.80/1.52  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.80/1.52  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 2.80/1.52  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.80/1.52  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.80/1.52  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.80/1.52  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_relat_1)).
% 2.80/1.52  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.52  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.80/1.52  tff(c_74, plain, (![A_23, B_24]: (k1_setfam_1(k2_tarski(A_23, B_24))=k3_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.52  tff(c_118, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_4, c_74])).
% 2.80/1.52  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.52  tff(c_124, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_118, c_8])).
% 2.80/1.52  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k7_relat_1(B_13, A_12), B_13) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.80/1.52  tff(c_93, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.52  tff(c_97, plain, (![B_13, A_12]: (k3_xboole_0(k7_relat_1(B_13, A_12), B_13)=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(resolution, [status(thm)], [c_12, c_93])).
% 2.80/1.52  tff(c_198, plain, (![B_13, A_12]: (k3_xboole_0(B_13, k7_relat_1(B_13, A_12))=k7_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_97])).
% 2.80/1.52  tff(c_14, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.52  tff(c_16, plain, (![A_16]: (k7_relat_1(A_16, k1_relat_1(A_16))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.80/1.52  tff(c_219, plain, (![C_39, A_40, B_41]: (k3_xboole_0(k7_relat_1(C_39, A_40), k7_relat_1(C_39, B_41))=k7_relat_1(C_39, k3_xboole_0(A_40, B_41)) | ~v1_relat_1(C_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.52  tff(c_303, plain, (![A_45, B_46]: (k7_relat_1(A_45, k3_xboole_0(k1_relat_1(A_45), B_46))=k3_xboole_0(A_45, k7_relat_1(A_45, B_46)) | ~v1_relat_1(A_45) | ~v1_relat_1(A_45))), inference(superposition, [status(thm), theory('equality')], [c_16, c_219])).
% 2.80/1.52  tff(c_846, plain, (![B_63, A_64]: (k7_relat_1(B_63, k1_relat_1(k7_relat_1(B_63, A_64)))=k3_xboole_0(B_63, k7_relat_1(B_63, A_64)) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_14, c_303])).
% 2.80/1.52  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.52  tff(c_174, plain, (![B_35, A_36]: (k3_xboole_0(k1_relat_1(B_35), A_36)=k1_relat_1(k7_relat_1(B_35, A_36)) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.80/1.52  tff(c_247, plain, (![A_42, B_43]: (k3_xboole_0(A_42, k1_relat_1(B_43))=k1_relat_1(k7_relat_1(B_43, A_42)) | ~v1_relat_1(B_43))), inference(superposition, [status(thm), theory('equality')], [c_174, c_124])).
% 2.80/1.52  tff(c_594, plain, (![B_59, B_58]: (k1_relat_1(k7_relat_1(B_59, k1_relat_1(B_58)))=k1_relat_1(k7_relat_1(B_58, k1_relat_1(B_59))) | ~v1_relat_1(B_59) | ~v1_relat_1(B_58))), inference(superposition, [status(thm), theory('equality')], [c_247, c_14])).
% 2.80/1.52  tff(c_18, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.80/1.52  tff(c_651, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_594, c_18])).
% 2.80/1.52  tff(c_690, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_22, c_651])).
% 2.80/1.52  tff(c_855, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_846, c_690])).
% 2.80/1.52  tff(c_912, plain, (k3_xboole_0('#skF_1', k7_relat_1('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_22, c_855])).
% 2.80/1.52  tff(c_916, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_198, c_912])).
% 2.80/1.52  tff(c_920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_916])).
% 2.80/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.80/1.52  
% 2.80/1.52  Inference rules
% 2.80/1.52  ----------------------
% 2.80/1.52  #Ref     : 0
% 2.80/1.52  #Sup     : 247
% 2.80/1.52  #Fact    : 0
% 2.80/1.52  #Define  : 0
% 2.80/1.52  #Split   : 0
% 2.80/1.52  #Chain   : 0
% 2.80/1.52  #Close   : 0
% 2.80/1.52  
% 2.80/1.52  Ordering : KBO
% 2.80/1.52  
% 2.80/1.52  Simplification rules
% 2.80/1.52  ----------------------
% 2.80/1.52  #Subsume      : 49
% 2.80/1.52  #Demod        : 30
% 2.80/1.52  #Tautology    : 76
% 2.80/1.52  #SimpNegUnit  : 0
% 2.80/1.52  #BackRed      : 0
% 2.80/1.52  
% 2.80/1.52  #Partial instantiations: 0
% 2.80/1.52  #Strategies tried      : 1
% 2.80/1.52  
% 2.80/1.52  Timing (in seconds)
% 2.80/1.52  ----------------------
% 2.80/1.52  Preprocessing        : 0.28
% 2.80/1.52  Parsing              : 0.15
% 2.80/1.52  CNF conversion       : 0.02
% 2.80/1.52  Main loop            : 0.37
% 2.80/1.52  Inferencing          : 0.15
% 2.80/1.52  Reduction            : 0.11
% 2.80/1.52  Demodulation         : 0.09
% 2.80/1.52  BG Simplification    : 0.02
% 2.80/1.52  Subsumption          : 0.06
% 2.80/1.52  Abstraction          : 0.02
% 2.80/1.52  MUC search           : 0.00
% 2.80/1.52  Cooper               : 0.00
% 2.80/1.52  Total                : 0.67
% 2.80/1.52  Index Insertion      : 0.00
% 2.80/1.52  Index Deletion       : 0.00
% 2.80/1.52  Index Matching       : 0.00
% 2.80/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
