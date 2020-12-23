%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 5.00s
% Output     : CNFRefutation 5.00s
% Verified   : 
% Statistics : Number of formulae       :   51 (  90 expanded)
%              Number of leaves         :   24 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 139 expanded)
%              Number of equality atoms :   20 (  50 expanded)
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

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    ! [A_36,B_37] : k1_setfam_1(k2_tarski(A_36,B_37)) = k3_xboole_0(B_37,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_62])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_97,plain,(
    ! [B_37,A_36] : k3_xboole_0(B_37,A_36) = k3_xboole_0(A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_10])).

tff(c_86,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = A_34
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_90,plain,(
    ! [B_21,A_20] :
      ( k3_xboole_0(k7_relat_1(B_21,A_20),B_21) = k7_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_20,c_86])).

tff(c_173,plain,(
    ! [B_47,A_48] :
      ( k3_xboole_0(B_47,k7_relat_1(B_47,A_48)) = k7_relat_1(B_47,A_48)
      | ~ v1_relat_1(B_47) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_90])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k3_xboole_0(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [B_47,A_48] :
      ( v1_relat_1(k7_relat_1(B_47,A_48))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_12])).

tff(c_213,plain,(
    ! [A_54,B_55] :
      ( r1_tarski(k1_relat_1(A_54),k1_relat_1(B_55))
      | ~ r1_tarski(A_54,B_55)
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    ! [B_23,A_22] :
      ( k7_relat_1(B_23,A_22) = B_23
      | ~ r1_tarski(k1_relat_1(B_23),A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_227,plain,(
    ! [A_58,B_59] :
      ( k7_relat_1(A_58,k1_relat_1(B_59)) = A_58
      | ~ r1_tarski(A_58,B_59)
      | ~ v1_relat_1(B_59)
      | ~ v1_relat_1(A_58) ) ),
    inference(resolution,[status(thm)],[c_213,c_22])).

tff(c_14,plain,(
    ! [C_16,A_14,B_15] :
      ( k7_relat_1(k7_relat_1(C_16,A_14),B_15) = k7_relat_1(C_16,k3_xboole_0(A_14,B_15))
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2698,plain,(
    ! [C_173,A_174,B_175] :
      ( k7_relat_1(C_173,k3_xboole_0(A_174,k1_relat_1(B_175))) = k7_relat_1(C_173,A_174)
      | ~ v1_relat_1(C_173)
      | ~ r1_tarski(k7_relat_1(C_173,A_174),B_175)
      | ~ v1_relat_1(B_175)
      | ~ v1_relat_1(k7_relat_1(C_173,A_174)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_227,c_14])).

tff(c_24,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_153,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_24])).

tff(c_2839,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2698,c_153])).

tff(c_2893,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2839])).

tff(c_2897,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2893])).

tff(c_2900,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_182,c_2897])).

tff(c_2904,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2900])).

tff(c_2905,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_2893])).

tff(c_2909,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_2905])).

tff(c_2913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:02:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.00/2.01  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/2.01  
% 5.00/2.01  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/2.02  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.00/2.02  
% 5.00/2.02  %Foreground sorts:
% 5.00/2.02  
% 5.00/2.02  
% 5.00/2.02  %Background operators:
% 5.00/2.02  
% 5.00/2.02  
% 5.00/2.02  %Foreground operators:
% 5.00/2.02  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.00/2.02  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.00/2.02  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.00/2.02  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.00/2.02  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.00/2.02  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.00/2.02  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.00/2.02  tff('#skF_2', type, '#skF_2': $i).
% 5.00/2.02  tff('#skF_1', type, '#skF_1': $i).
% 5.00/2.02  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.00/2.02  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.00/2.02  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.00/2.02  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.00/2.02  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.00/2.02  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.00/2.02  
% 5.00/2.03  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 5.00/2.03  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 5.00/2.03  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.00/2.03  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.00/2.03  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.00/2.03  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 5.00/2.03  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.00/2.03  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 5.00/2.03  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 5.00/2.03  tff(c_26, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/2.03  tff(c_20, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.00/2.03  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.00/2.03  tff(c_62, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.00/2.03  tff(c_91, plain, (![A_36, B_37]: (k1_setfam_1(k2_tarski(A_36, B_37))=k3_xboole_0(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_4, c_62])).
% 5.00/2.03  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.00/2.03  tff(c_97, plain, (![B_37, A_36]: (k3_xboole_0(B_37, A_36)=k3_xboole_0(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_91, c_10])).
% 5.00/2.03  tff(c_86, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=A_34 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.00/2.03  tff(c_90, plain, (![B_21, A_20]: (k3_xboole_0(k7_relat_1(B_21, A_20), B_21)=k7_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_20, c_86])).
% 5.00/2.03  tff(c_173, plain, (![B_47, A_48]: (k3_xboole_0(B_47, k7_relat_1(B_47, A_48))=k7_relat_1(B_47, A_48) | ~v1_relat_1(B_47))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_90])).
% 5.00/2.03  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k3_xboole_0(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.00/2.03  tff(c_182, plain, (![B_47, A_48]: (v1_relat_1(k7_relat_1(B_47, A_48)) | ~v1_relat_1(B_47) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_173, c_12])).
% 5.00/2.03  tff(c_213, plain, (![A_54, B_55]: (r1_tarski(k1_relat_1(A_54), k1_relat_1(B_55)) | ~r1_tarski(A_54, B_55) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.00/2.03  tff(c_22, plain, (![B_23, A_22]: (k7_relat_1(B_23, A_22)=B_23 | ~r1_tarski(k1_relat_1(B_23), A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.00/2.03  tff(c_227, plain, (![A_58, B_59]: (k7_relat_1(A_58, k1_relat_1(B_59))=A_58 | ~r1_tarski(A_58, B_59) | ~v1_relat_1(B_59) | ~v1_relat_1(A_58))), inference(resolution, [status(thm)], [c_213, c_22])).
% 5.00/2.03  tff(c_14, plain, (![C_16, A_14, B_15]: (k7_relat_1(k7_relat_1(C_16, A_14), B_15)=k7_relat_1(C_16, k3_xboole_0(A_14, B_15)) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.00/2.03  tff(c_2698, plain, (![C_173, A_174, B_175]: (k7_relat_1(C_173, k3_xboole_0(A_174, k1_relat_1(B_175)))=k7_relat_1(C_173, A_174) | ~v1_relat_1(C_173) | ~r1_tarski(k7_relat_1(C_173, A_174), B_175) | ~v1_relat_1(B_175) | ~v1_relat_1(k7_relat_1(C_173, A_174)))), inference(superposition, [status(thm), theory('equality')], [c_227, c_14])).
% 5.00/2.03  tff(c_24, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.00/2.03  tff(c_153, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_97, c_24])).
% 5.00/2.03  tff(c_2839, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2698, c_153])).
% 5.00/2.03  tff(c_2893, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2839])).
% 5.00/2.03  tff(c_2897, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_2893])).
% 5.00/2.03  tff(c_2900, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_182, c_2897])).
% 5.00/2.03  tff(c_2904, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2900])).
% 5.00/2.03  tff(c_2905, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(splitRight, [status(thm)], [c_2893])).
% 5.00/2.03  tff(c_2909, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_20, c_2905])).
% 5.00/2.03  tff(c_2913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_2909])).
% 5.00/2.03  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.00/2.03  
% 5.00/2.03  Inference rules
% 5.00/2.03  ----------------------
% 5.00/2.03  #Ref     : 0
% 5.00/2.03  #Sup     : 847
% 5.00/2.03  #Fact    : 0
% 5.00/2.03  #Define  : 0
% 5.00/2.03  #Split   : 1
% 5.00/2.03  #Chain   : 0
% 5.00/2.03  #Close   : 0
% 5.00/2.03  
% 5.00/2.03  Ordering : KBO
% 5.00/2.03  
% 5.00/2.03  Simplification rules
% 5.00/2.03  ----------------------
% 5.00/2.03  #Subsume      : 172
% 5.00/2.03  #Demod        : 46
% 5.00/2.03  #Tautology    : 105
% 5.00/2.03  #SimpNegUnit  : 0
% 5.00/2.03  #BackRed      : 0
% 5.00/2.03  
% 5.00/2.03  #Partial instantiations: 0
% 5.00/2.03  #Strategies tried      : 1
% 5.00/2.03  
% 5.00/2.03  Timing (in seconds)
% 5.00/2.03  ----------------------
% 5.00/2.03  Preprocessing        : 0.31
% 5.00/2.03  Parsing              : 0.16
% 5.00/2.03  CNF conversion       : 0.02
% 5.00/2.03  Main loop            : 0.89
% 5.00/2.03  Inferencing          : 0.33
% 5.00/2.03  Reduction            : 0.25
% 5.00/2.03  Demodulation         : 0.19
% 5.00/2.03  BG Simplification    : 0.05
% 5.00/2.03  Subsumption          : 0.21
% 5.00/2.03  Abstraction          : 0.05
% 5.00/2.03  MUC search           : 0.00
% 5.00/2.03  Cooper               : 0.00
% 5.00/2.03  Total                : 1.23
% 5.00/2.03  Index Insertion      : 0.00
% 5.00/2.03  Index Deletion       : 0.00
% 5.00/2.03  Index Matching       : 0.00
% 5.00/2.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------
