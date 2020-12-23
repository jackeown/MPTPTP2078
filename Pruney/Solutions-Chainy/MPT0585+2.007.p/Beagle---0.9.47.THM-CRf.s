%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:01 EST 2020

% Result     : Theorem 2.15s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   39 (  46 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    9
%              Number of atoms          :   53 (  69 expanded)
%              Number of equality atoms :   17 (  22 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k7_relat_1(A_5,B_6))
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_11,A_10)),A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_135,plain,(
    ! [C_30,B_31,A_32] :
      ( k7_relat_1(k7_relat_1(C_30,B_31),A_32) = k7_relat_1(C_30,A_32)
      | ~ r1_tarski(A_32,B_31)
      | ~ v1_relat_1(C_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_14] :
      ( k7_relat_1(A_14,k1_relat_1(A_14)) = A_14
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_168,plain,(
    ! [C_33,B_34] :
      ( k7_relat_1(C_33,k1_relat_1(k7_relat_1(C_33,B_34))) = k7_relat_1(C_33,B_34)
      | ~ v1_relat_1(k7_relat_1(C_33,B_34))
      | ~ r1_tarski(k1_relat_1(k7_relat_1(C_33,B_34)),B_34)
      | ~ v1_relat_1(C_33) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_14])).

tff(c_321,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,k1_relat_1(k7_relat_1(B_39,A_40))) = k7_relat_1(B_39,A_40)
      | ~ v1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_168])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_81,plain,(
    ! [B_26,A_27] :
      ( k3_xboole_0(k1_relat_1(B_26),A_27) = k1_relat_1(k7_relat_1(B_26,A_27))
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,k1_relat_1(B_29)) = k1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_2])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( k3_xboole_0(k1_relat_1(B_13),A_12) = k1_relat_1(k7_relat_1(B_13,A_12))
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_176,plain,(
    ! [B_36,B_35] :
      ( k1_relat_1(k7_relat_1(B_36,k1_relat_1(B_35))) = k1_relat_1(k7_relat_1(B_35,k1_relat_1(B_36)))
      | ~ v1_relat_1(B_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_12])).

tff(c_16,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_2',k1_relat_1('#skF_1')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_213,plain,
    ( k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_16])).

tff(c_284,plain,(
    k7_relat_1('#skF_1',k1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))) != k7_relat_1('#skF_1',k1_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_213])).

tff(c_333,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_284])).

tff(c_373,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_1',k1_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_333])).

tff(c_379,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_6,c_373])).

tff(c_383,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:39:54 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.15/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  
% 2.15/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.15/1.24  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.15/1.24  
% 2.15/1.24  %Foreground sorts:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Background operators:
% 2.15/1.24  
% 2.15/1.24  
% 2.15/1.24  %Foreground operators:
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.15/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.15/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.15/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.15/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.15/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.15/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.15/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.15/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.15/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.15/1.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.15/1.24  
% 2.21/1.25  tff(f_59, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k7_relat_1(A, k1_relat_1(B)) = k7_relat_1(A, k1_relat_1(k7_relat_1(B, k1_relat_1(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t189_relat_1)).
% 2.21/1.25  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.21/1.25  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.21/1.25  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 2.21/1.25  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_relat_1)).
% 2.21/1.25  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.21/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.21/1.25  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.21/1.25  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k7_relat_1(A_5, B_6)) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.21/1.25  tff(c_10, plain, (![B_11, A_10]: (r1_tarski(k1_relat_1(k7_relat_1(B_11, A_10)), A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.21/1.25  tff(c_135, plain, (![C_30, B_31, A_32]: (k7_relat_1(k7_relat_1(C_30, B_31), A_32)=k7_relat_1(C_30, A_32) | ~r1_tarski(A_32, B_31) | ~v1_relat_1(C_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.21/1.25  tff(c_14, plain, (![A_14]: (k7_relat_1(A_14, k1_relat_1(A_14))=A_14 | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.21/1.25  tff(c_168, plain, (![C_33, B_34]: (k7_relat_1(C_33, k1_relat_1(k7_relat_1(C_33, B_34)))=k7_relat_1(C_33, B_34) | ~v1_relat_1(k7_relat_1(C_33, B_34)) | ~r1_tarski(k1_relat_1(k7_relat_1(C_33, B_34)), B_34) | ~v1_relat_1(C_33))), inference(superposition, [status(thm), theory('equality')], [c_135, c_14])).
% 2.21/1.25  tff(c_321, plain, (![B_39, A_40]: (k7_relat_1(B_39, k1_relat_1(k7_relat_1(B_39, A_40)))=k7_relat_1(B_39, A_40) | ~v1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(resolution, [status(thm)], [c_10, c_168])).
% 2.21/1.25  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.21/1.25  tff(c_81, plain, (![B_26, A_27]: (k3_xboole_0(k1_relat_1(B_26), A_27)=k1_relat_1(k7_relat_1(B_26, A_27)) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.21/1.25  tff(c_104, plain, (![A_28, B_29]: (k3_xboole_0(A_28, k1_relat_1(B_29))=k1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(superposition, [status(thm), theory('equality')], [c_81, c_2])).
% 2.21/1.25  tff(c_12, plain, (![B_13, A_12]: (k3_xboole_0(k1_relat_1(B_13), A_12)=k1_relat_1(k7_relat_1(B_13, A_12)) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.21/1.25  tff(c_176, plain, (![B_36, B_35]: (k1_relat_1(k7_relat_1(B_36, k1_relat_1(B_35)))=k1_relat_1(k7_relat_1(B_35, k1_relat_1(B_36))) | ~v1_relat_1(B_36) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_104, c_12])).
% 2.21/1.25  tff(c_16, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_2', k1_relat_1('#skF_1'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.21/1.25  tff(c_213, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_176, c_16])).
% 2.21/1.25  tff(c_284, plain, (k7_relat_1('#skF_1', k1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))))!=k7_relat_1('#skF_1', k1_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_213])).
% 2.21/1.25  tff(c_333, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_321, c_284])).
% 2.21/1.25  tff(c_373, plain, (~v1_relat_1(k7_relat_1('#skF_1', k1_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_333])).
% 2.21/1.25  tff(c_379, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_6, c_373])).
% 2.21/1.25  tff(c_383, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_379])).
% 2.21/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.25  
% 2.21/1.25  Inference rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Ref     : 0
% 2.21/1.25  #Sup     : 99
% 2.21/1.25  #Fact    : 0
% 2.21/1.25  #Define  : 0
% 2.21/1.25  #Split   : 0
% 2.21/1.25  #Chain   : 0
% 2.21/1.25  #Close   : 0
% 2.21/1.25  
% 2.21/1.25  Ordering : KBO
% 2.21/1.25  
% 2.21/1.25  Simplification rules
% 2.21/1.25  ----------------------
% 2.21/1.25  #Subsume      : 17
% 2.21/1.25  #Demod        : 6
% 2.21/1.25  #Tautology    : 33
% 2.21/1.26  #SimpNegUnit  : 0
% 2.21/1.26  #BackRed      : 0
% 2.21/1.26  
% 2.21/1.26  #Partial instantiations: 0
% 2.21/1.26  #Strategies tried      : 1
% 2.21/1.26  
% 2.21/1.26  Timing (in seconds)
% 2.21/1.26  ----------------------
% 2.21/1.26  Preprocessing        : 0.28
% 2.21/1.26  Parsing              : 0.15
% 2.21/1.26  CNF conversion       : 0.02
% 2.21/1.26  Main loop            : 0.22
% 2.21/1.26  Inferencing          : 0.09
% 2.21/1.26  Reduction            : 0.06
% 2.21/1.26  Demodulation         : 0.05
% 2.21/1.26  BG Simplification    : 0.02
% 2.21/1.26  Subsumption          : 0.04
% 2.21/1.26  Abstraction          : 0.02
% 2.21/1.26  MUC search           : 0.00
% 2.21/1.26  Cooper               : 0.00
% 2.21/1.26  Total                : 0.52
% 2.21/1.26  Index Insertion      : 0.00
% 2.21/1.26  Index Deletion       : 0.00
% 2.21/1.26  Index Matching       : 0.00
% 2.21/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
