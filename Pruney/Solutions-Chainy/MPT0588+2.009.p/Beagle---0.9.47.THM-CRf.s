%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 2.70s
% Output     : CNFRefutation 2.70s
% Verified   : 
% Statistics : Number of formulae       :   46 (  75 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   59 ( 116 expanded)
%              Number of equality atoms :   16 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_18,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k7_relat_1(B_19,A_18),B_19)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_14,A_12,B_13] :
      ( k7_relat_1(k7_relat_1(C_14,A_12),B_13) = k7_relat_1(C_14,k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_152,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_relat_1(A_41),k1_relat_1(B_42))
      | ~ r1_tarski(A_41,B_42)
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( k7_relat_1(B_21,A_20) = B_21
      | ~ r1_tarski(k1_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_179,plain,(
    ! [A_48,B_49] :
      ( k7_relat_1(A_48,k1_relat_1(B_49)) = A_48
      | ~ r1_tarski(A_48,B_49)
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(A_48) ) ),
    inference(resolution,[status(thm)],[c_152,c_20])).

tff(c_615,plain,(
    ! [C_80,A_81,B_82] :
      ( k7_relat_1(C_80,k3_xboole_0(A_81,k1_relat_1(B_82))) = k7_relat_1(C_80,A_81)
      | ~ r1_tarski(k7_relat_1(C_80,A_81),B_82)
      | ~ v1_relat_1(B_82)
      | ~ v1_relat_1(k7_relat_1(C_80,A_81))
      | ~ v1_relat_1(C_80) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_179])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_60,plain,(
    ! [A_28,B_29] : k1_setfam_1(k2_tarski(A_28,B_29)) = k3_xboole_0(A_28,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_84,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(B_33,A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_60])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [B_33,A_32] : k3_xboole_0(B_33,A_32) = k3_xboole_0(A_32,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_8])).

tff(c_22,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_140,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_22])).

tff(c_667,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_140])).

tff(c_708,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_667])).

tff(c_711,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_836,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_711])).

tff(c_840,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_836])).

tff(c_841,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_845,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_841])).

tff(c_849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_845])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:54:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.70/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.43  
% 2.70/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.44  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.70/1.44  
% 2.70/1.44  %Foreground sorts:
% 2.70/1.44  
% 2.70/1.44  
% 2.70/1.44  %Background operators:
% 2.70/1.44  
% 2.70/1.44  
% 2.70/1.44  %Foreground operators:
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.70/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.70/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.70/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.70/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.70/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.70/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.70/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.70/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.70/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.70/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.70/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.70/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.70/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.70/1.44  
% 2.70/1.45  tff(f_67, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 2.70/1.45  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 2.70/1.45  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.70/1.45  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.70/1.45  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 2.70/1.45  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.70/1.45  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.70/1.45  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.70/1.45  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.45  tff(c_18, plain, (![B_19, A_18]: (r1_tarski(k7_relat_1(B_19, A_18), B_19) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.70/1.45  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.70/1.45  tff(c_12, plain, (![C_14, A_12, B_13]: (k7_relat_1(k7_relat_1(C_14, A_12), B_13)=k7_relat_1(C_14, k3_xboole_0(A_12, B_13)) | ~v1_relat_1(C_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.70/1.45  tff(c_152, plain, (![A_41, B_42]: (r1_tarski(k1_relat_1(A_41), k1_relat_1(B_42)) | ~r1_tarski(A_41, B_42) | ~v1_relat_1(B_42) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.70/1.45  tff(c_20, plain, (![B_21, A_20]: (k7_relat_1(B_21, A_20)=B_21 | ~r1_tarski(k1_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.70/1.45  tff(c_179, plain, (![A_48, B_49]: (k7_relat_1(A_48, k1_relat_1(B_49))=A_48 | ~r1_tarski(A_48, B_49) | ~v1_relat_1(B_49) | ~v1_relat_1(A_48))), inference(resolution, [status(thm)], [c_152, c_20])).
% 2.70/1.45  tff(c_615, plain, (![C_80, A_81, B_82]: (k7_relat_1(C_80, k3_xboole_0(A_81, k1_relat_1(B_82)))=k7_relat_1(C_80, A_81) | ~r1_tarski(k7_relat_1(C_80, A_81), B_82) | ~v1_relat_1(B_82) | ~v1_relat_1(k7_relat_1(C_80, A_81)) | ~v1_relat_1(C_80))), inference(superposition, [status(thm), theory('equality')], [c_12, c_179])).
% 2.70/1.45  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.70/1.45  tff(c_60, plain, (![A_28, B_29]: (k1_setfam_1(k2_tarski(A_28, B_29))=k3_xboole_0(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.45  tff(c_84, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(B_33, A_32))), inference(superposition, [status(thm), theory('equality')], [c_2, c_60])).
% 2.70/1.45  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.70/1.45  tff(c_90, plain, (![B_33, A_32]: (k3_xboole_0(B_33, A_32)=k3_xboole_0(A_32, B_33))), inference(superposition, [status(thm), theory('equality')], [c_84, c_8])).
% 2.70/1.45  tff(c_22, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.70/1.45  tff(c_140, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_22])).
% 2.70/1.45  tff(c_667, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_615, c_140])).
% 2.70/1.45  tff(c_708, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_667])).
% 2.70/1.45  tff(c_711, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_708])).
% 2.70/1.45  tff(c_836, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_711])).
% 2.70/1.45  tff(c_840, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_836])).
% 2.70/1.45  tff(c_841, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_708])).
% 2.70/1.45  tff(c_845, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_18, c_841])).
% 2.70/1.45  tff(c_849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_845])).
% 2.70/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.70/1.45  
% 2.70/1.45  Inference rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Ref     : 0
% 2.70/1.45  #Sup     : 223
% 2.70/1.45  #Fact    : 0
% 2.70/1.45  #Define  : 0
% 2.70/1.45  #Split   : 1
% 2.70/1.45  #Chain   : 0
% 2.70/1.45  #Close   : 0
% 2.70/1.45  
% 2.70/1.45  Ordering : KBO
% 2.70/1.45  
% 2.70/1.45  Simplification rules
% 2.70/1.45  ----------------------
% 2.70/1.45  #Subsume      : 34
% 2.70/1.45  #Demod        : 8
% 2.70/1.45  #Tautology    : 46
% 2.70/1.45  #SimpNegUnit  : 0
% 2.70/1.45  #BackRed      : 0
% 2.70/1.45  
% 2.70/1.45  #Partial instantiations: 0
% 2.70/1.45  #Strategies tried      : 1
% 2.70/1.45  
% 2.70/1.45  Timing (in seconds)
% 2.70/1.45  ----------------------
% 2.70/1.45  Preprocessing        : 0.29
% 2.70/1.45  Parsing              : 0.16
% 2.70/1.45  CNF conversion       : 0.02
% 2.70/1.45  Main loop            : 0.40
% 2.70/1.45  Inferencing          : 0.16
% 2.70/1.45  Reduction            : 0.12
% 2.70/1.45  Demodulation         : 0.09
% 2.70/1.45  BG Simplification    : 0.03
% 2.70/1.45  Subsumption          : 0.08
% 2.70/1.45  Abstraction          : 0.03
% 2.70/1.45  MUC search           : 0.00
% 2.70/1.45  Cooper               : 0.00
% 2.70/1.45  Total                : 0.72
% 2.70/1.45  Index Insertion      : 0.00
% 2.70/1.45  Index Deletion       : 0.00
% 2.70/1.45  Index Matching       : 0.00
% 2.70/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
