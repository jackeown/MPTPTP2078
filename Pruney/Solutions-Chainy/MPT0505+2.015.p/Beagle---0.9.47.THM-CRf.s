%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:52 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.22s
% Verified   : 
% Statistics : Number of formulae       :   46 (  54 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  57 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_68,negated_conjecture,(
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

tff(f_43,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_32,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_22,plain,(
    ! [A_36] : k1_relat_1(k6_relat_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [A_32] : v1_relat_1(k6_relat_1(A_32)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_114,plain,(
    ! [B_53,A_54] :
      ( k7_relat_1(B_53,A_54) = B_53
      | ~ r1_tarski(k1_relat_1(B_53),A_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_117,plain,(
    ! [A_36,A_54] :
      ( k7_relat_1(k6_relat_1(A_36),A_54) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_54)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_114])).

tff(c_119,plain,(
    ! [A_36,A_54] :
      ( k7_relat_1(k6_relat_1(A_36),A_54) = k6_relat_1(A_36)
      | ~ r1_tarski(A_36,A_54) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_117])).

tff(c_129,plain,(
    ! [B_57,A_58] :
      ( k3_xboole_0(k1_relat_1(B_57),A_58) = k1_relat_1(k7_relat_1(B_57,A_58))
      | ~ v1_relat_1(B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_152,plain,(
    ! [A_36,A_58] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_36),A_58)) = k3_xboole_0(A_36,A_58)
      | ~ v1_relat_1(k6_relat_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_129])).

tff(c_157,plain,(
    ! [A_59,A_60] : k1_relat_1(k7_relat_1(k6_relat_1(A_59),A_60)) = k3_xboole_0(A_59,A_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_152])).

tff(c_172,plain,(
    ! [A_36,A_54] :
      ( k3_xboole_0(A_36,A_54) = k1_relat_1(k6_relat_1(A_36))
      | ~ r1_tarski(A_36,A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_157])).

tff(c_176,plain,(
    ! [A_61,A_62] :
      ( k3_xboole_0(A_61,A_62) = A_61
      | ~ r1_tarski(A_61,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_172])).

tff(c_180,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_32,c_176])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_233,plain,(
    ! [C_69,A_70,B_71] :
      ( k7_relat_1(k7_relat_1(C_69,A_70),B_71) = k7_relat_1(C_69,k3_xboole_0(A_70,B_71))
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_30,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_2'),'#skF_1') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_242,plain,
    ( k7_relat_1('#skF_3',k3_xboole_0('#skF_2','#skF_1')) != k7_relat_1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_30])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_180,c_2,c_242])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:36:26 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.20  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.21  
% 2.22/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.21  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.22/1.21  
% 2.22/1.21  %Foreground sorts:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Background operators:
% 2.22/1.21  
% 2.22/1.21  
% 2.22/1.21  %Foreground operators:
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.22/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.22/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.22/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.22/1.21  tff('#skF_3', type, '#skF_3': $i).
% 2.22/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.22/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.22/1.21  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.22/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.22/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.22/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.22/1.21  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.22/1.21  
% 2.22/1.22  tff(f_68, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_relat_1)).
% 2.22/1.22  tff(f_51, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.22/1.22  tff(f_43, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.22/1.22  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.22/1.22  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 2.22/1.22  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.22/1.22  tff(f_47, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.22/1.22  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.22  tff(c_32, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.22  tff(c_22, plain, (![A_36]: (k1_relat_1(k6_relat_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.22/1.22  tff(c_18, plain, (![A_32]: (v1_relat_1(k6_relat_1(A_32)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.22/1.22  tff(c_114, plain, (![B_53, A_54]: (k7_relat_1(B_53, A_54)=B_53 | ~r1_tarski(k1_relat_1(B_53), A_54) | ~v1_relat_1(B_53))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.22/1.22  tff(c_117, plain, (![A_36, A_54]: (k7_relat_1(k6_relat_1(A_36), A_54)=k6_relat_1(A_36) | ~r1_tarski(A_36, A_54) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_114])).
% 2.22/1.22  tff(c_119, plain, (![A_36, A_54]: (k7_relat_1(k6_relat_1(A_36), A_54)=k6_relat_1(A_36) | ~r1_tarski(A_36, A_54))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_117])).
% 2.22/1.22  tff(c_129, plain, (![B_57, A_58]: (k3_xboole_0(k1_relat_1(B_57), A_58)=k1_relat_1(k7_relat_1(B_57, A_58)) | ~v1_relat_1(B_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.22/1.22  tff(c_152, plain, (![A_36, A_58]: (k1_relat_1(k7_relat_1(k6_relat_1(A_36), A_58))=k3_xboole_0(A_36, A_58) | ~v1_relat_1(k6_relat_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_129])).
% 2.22/1.22  tff(c_157, plain, (![A_59, A_60]: (k1_relat_1(k7_relat_1(k6_relat_1(A_59), A_60))=k3_xboole_0(A_59, A_60))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_152])).
% 2.22/1.22  tff(c_172, plain, (![A_36, A_54]: (k3_xboole_0(A_36, A_54)=k1_relat_1(k6_relat_1(A_36)) | ~r1_tarski(A_36, A_54))), inference(superposition, [status(thm), theory('equality')], [c_119, c_157])).
% 2.22/1.22  tff(c_176, plain, (![A_61, A_62]: (k3_xboole_0(A_61, A_62)=A_61 | ~r1_tarski(A_61, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_172])).
% 2.22/1.22  tff(c_180, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_32, c_176])).
% 2.22/1.22  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.22/1.22  tff(c_233, plain, (![C_69, A_70, B_71]: (k7_relat_1(k7_relat_1(C_69, A_70), B_71)=k7_relat_1(C_69, k3_xboole_0(A_70, B_71)) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.22/1.22  tff(c_30, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_2'), '#skF_1')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.22/1.22  tff(c_242, plain, (k7_relat_1('#skF_3', k3_xboole_0('#skF_2', '#skF_1'))!=k7_relat_1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_233, c_30])).
% 2.22/1.22  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_180, c_2, c_242])).
% 2.22/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.22  
% 2.22/1.22  Inference rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Ref     : 0
% 2.22/1.22  #Sup     : 54
% 2.22/1.22  #Fact    : 0
% 2.22/1.22  #Define  : 0
% 2.22/1.22  #Split   : 0
% 2.22/1.22  #Chain   : 0
% 2.22/1.22  #Close   : 0
% 2.22/1.22  
% 2.22/1.22  Ordering : KBO
% 2.22/1.22  
% 2.22/1.22  Simplification rules
% 2.22/1.22  ----------------------
% 2.22/1.22  #Subsume      : 6
% 2.22/1.22  #Demod        : 8
% 2.22/1.22  #Tautology    : 31
% 2.22/1.22  #SimpNegUnit  : 0
% 2.22/1.22  #BackRed      : 0
% 2.22/1.22  
% 2.22/1.22  #Partial instantiations: 0
% 2.22/1.22  #Strategies tried      : 1
% 2.22/1.22  
% 2.22/1.22  Timing (in seconds)
% 2.22/1.22  ----------------------
% 2.22/1.22  Preprocessing        : 0.31
% 2.22/1.22  Parsing              : 0.16
% 2.22/1.22  CNF conversion       : 0.02
% 2.22/1.22  Main loop            : 0.16
% 2.22/1.22  Inferencing          : 0.07
% 2.22/1.22  Reduction            : 0.05
% 2.22/1.22  Demodulation         : 0.04
% 2.22/1.22  BG Simplification    : 0.01
% 2.22/1.22  Subsumption          : 0.02
% 2.22/1.22  Abstraction          : 0.01
% 2.22/1.22  MUC search           : 0.00
% 2.22/1.22  Cooper               : 0.00
% 2.22/1.23  Total                : 0.49
% 2.22/1.23  Index Insertion      : 0.00
% 2.22/1.23  Index Deletion       : 0.00
% 2.22/1.23  Index Matching       : 0.00
% 2.22/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
