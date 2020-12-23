%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:44 EST 2020

% Result     : Theorem 2.00s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   45 (  50 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   53 (  60 expanded)
%              Number of equality atoms :   22 (  25 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_31,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7] :
      ( k2_xboole_0(k1_relat_1(A_7),k2_relat_1(A_7)) = k3_relat_1(A_7)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_53,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [B_21,A_22] : k3_tarski(k2_tarski(B_21,A_22)) = k2_xboole_0(A_22,B_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_53])).

tff(c_6,plain,(
    ! [A_5,B_6] : k3_tarski(k2_tarski(A_5,B_6)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [B_23,A_24] : k2_xboole_0(B_23,A_24) = k2_xboole_0(A_24,B_23) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(A_1,k2_xboole_0(A_1,B_2)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(B_26,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_2])).

tff(c_151,plain,(
    ! [A_7] :
      ( r1_tarski(k2_relat_1(A_7),k3_relat_1(A_7))
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_142])).

tff(c_167,plain,(
    ! [A_31,B_32] :
      ( k8_relat_1(A_31,B_32) = B_32
      | ~ r1_tarski(k2_relat_1(B_32),A_31)
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_182,plain,(
    ! [A_33] :
      ( k8_relat_1(k3_relat_1(A_33),A_33) = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(resolution,[status(thm)],[c_151,c_167])).

tff(c_14,plain,(
    ! [A_12,B_13] :
      ( k7_relat_1(k8_relat_1(A_12,B_13),A_12) = k2_wellord1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_345,plain,(
    ! [A_47] :
      ( k7_relat_1(A_47,k3_relat_1(A_47)) = k2_wellord1(A_47,k3_relat_1(A_47))
      | ~ v1_relat_1(A_47)
      | ~ v1_relat_1(A_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_14])).

tff(c_68,plain,(
    ! [A_20] :
      ( k2_xboole_0(k1_relat_1(A_20),k2_relat_1(A_20)) = k3_relat_1(A_20)
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_20] :
      ( r1_tarski(k1_relat_1(A_20),k3_relat_1(A_20))
      | ~ v1_relat_1(A_20) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_2])).

tff(c_247,plain,(
    ! [B_38,A_39] :
      ( k7_relat_1(B_38,A_39) = B_38
      | ~ r1_tarski(k1_relat_1(B_38),A_39)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_259,plain,(
    ! [A_20] :
      ( k7_relat_1(A_20,k3_relat_1(A_20)) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_74,c_247])).

tff(c_398,plain,(
    ! [A_50] :
      ( k2_wellord1(A_50,k3_relat_1(A_50)) = A_50
      | ~ v1_relat_1(A_50)
      | ~ v1_relat_1(A_50)
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_259])).

tff(c_16,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_404,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_16])).

tff(c_412,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:18:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.00/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.00/1.24  
% 2.00/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.24  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 2.14/1.24  
% 2.14/1.24  %Foreground sorts:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Background operators:
% 2.14/1.24  
% 2.14/1.24  
% 2.14/1.24  %Foreground operators:
% 2.14/1.24  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.24  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.14/1.24  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.14/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.24  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.14/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.14/1.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.14/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.24  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.14/1.24  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.14/1.24  
% 2.14/1.25  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 2.14/1.25  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.14/1.25  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.14/1.25  tff(f_31, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.14/1.25  tff(f_27, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.14/1.25  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.14/1.25  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 2.14/1.25  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.14/1.25  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.25  tff(c_8, plain, (![A_7]: (k2_xboole_0(k1_relat_1(A_7), k2_relat_1(A_7))=k3_relat_1(A_7) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.25  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.14/1.25  tff(c_53, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.25  tff(c_80, plain, (![B_21, A_22]: (k3_tarski(k2_tarski(B_21, A_22))=k2_xboole_0(A_22, B_21))), inference(superposition, [status(thm), theory('equality')], [c_4, c_53])).
% 2.14/1.25  tff(c_6, plain, (![A_5, B_6]: (k3_tarski(k2_tarski(A_5, B_6))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.25  tff(c_103, plain, (![B_23, A_24]: (k2_xboole_0(B_23, A_24)=k2_xboole_0(A_24, B_23))), inference(superposition, [status(thm), theory('equality')], [c_80, c_6])).
% 2.14/1.25  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.25  tff(c_142, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(B_26, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_2])).
% 2.14/1.25  tff(c_151, plain, (![A_7]: (r1_tarski(k2_relat_1(A_7), k3_relat_1(A_7)) | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_142])).
% 2.14/1.25  tff(c_167, plain, (![A_31, B_32]: (k8_relat_1(A_31, B_32)=B_32 | ~r1_tarski(k2_relat_1(B_32), A_31) | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.25  tff(c_182, plain, (![A_33]: (k8_relat_1(k3_relat_1(A_33), A_33)=A_33 | ~v1_relat_1(A_33))), inference(resolution, [status(thm)], [c_151, c_167])).
% 2.14/1.25  tff(c_14, plain, (![A_12, B_13]: (k7_relat_1(k8_relat_1(A_12, B_13), A_12)=k2_wellord1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.25  tff(c_345, plain, (![A_47]: (k7_relat_1(A_47, k3_relat_1(A_47))=k2_wellord1(A_47, k3_relat_1(A_47)) | ~v1_relat_1(A_47) | ~v1_relat_1(A_47))), inference(superposition, [status(thm), theory('equality')], [c_182, c_14])).
% 2.14/1.25  tff(c_68, plain, (![A_20]: (k2_xboole_0(k1_relat_1(A_20), k2_relat_1(A_20))=k3_relat_1(A_20) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.25  tff(c_74, plain, (![A_20]: (r1_tarski(k1_relat_1(A_20), k3_relat_1(A_20)) | ~v1_relat_1(A_20))), inference(superposition, [status(thm), theory('equality')], [c_68, c_2])).
% 2.14/1.25  tff(c_247, plain, (![B_38, A_39]: (k7_relat_1(B_38, A_39)=B_38 | ~r1_tarski(k1_relat_1(B_38), A_39) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.14/1.25  tff(c_259, plain, (![A_20]: (k7_relat_1(A_20, k3_relat_1(A_20))=A_20 | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_74, c_247])).
% 2.14/1.25  tff(c_398, plain, (![A_50]: (k2_wellord1(A_50, k3_relat_1(A_50))=A_50 | ~v1_relat_1(A_50) | ~v1_relat_1(A_50) | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_345, c_259])).
% 2.14/1.25  tff(c_16, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.14/1.25  tff(c_404, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_398, c_16])).
% 2.14/1.25  tff(c_412, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_404])).
% 2.14/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.25  
% 2.14/1.25  Inference rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Ref     : 0
% 2.14/1.25  #Sup     : 93
% 2.14/1.25  #Fact    : 0
% 2.14/1.25  #Define  : 0
% 2.14/1.25  #Split   : 0
% 2.14/1.25  #Chain   : 0
% 2.14/1.25  #Close   : 0
% 2.14/1.25  
% 2.14/1.25  Ordering : KBO
% 2.14/1.25  
% 2.14/1.25  Simplification rules
% 2.14/1.25  ----------------------
% 2.14/1.25  #Subsume      : 11
% 2.14/1.25  #Demod        : 9
% 2.14/1.25  #Tautology    : 55
% 2.14/1.25  #SimpNegUnit  : 0
% 2.14/1.25  #BackRed      : 0
% 2.14/1.25  
% 2.14/1.25  #Partial instantiations: 0
% 2.14/1.25  #Strategies tried      : 1
% 2.14/1.25  
% 2.14/1.25  Timing (in seconds)
% 2.14/1.25  ----------------------
% 2.14/1.26  Preprocessing        : 0.27
% 2.14/1.26  Parsing              : 0.15
% 2.14/1.26  CNF conversion       : 0.02
% 2.14/1.26  Main loop            : 0.22
% 2.14/1.26  Inferencing          : 0.09
% 2.14/1.26  Reduction            : 0.07
% 2.14/1.26  Demodulation         : 0.06
% 2.14/1.26  BG Simplification    : 0.01
% 2.14/1.26  Subsumption          : 0.03
% 2.14/1.26  Abstraction          : 0.01
% 2.14/1.26  MUC search           : 0.00
% 2.14/1.26  Cooper               : 0.00
% 2.14/1.26  Total                : 0.51
% 2.14/1.26  Index Insertion      : 0.00
% 2.14/1.26  Index Deletion       : 0.00
% 2.14/1.26  Index Matching       : 0.00
% 2.14/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
