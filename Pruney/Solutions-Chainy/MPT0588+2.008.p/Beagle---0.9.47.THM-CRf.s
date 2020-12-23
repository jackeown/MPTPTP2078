%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:04 EST 2020

% Result     : Theorem 3.21s
% Output     : CNFRefutation 3.33s
% Verified   : 
% Statistics : Number of formulae       :   41 (  45 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  52 expanded)
%              Number of equality atoms :   18 (  21 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t192_relat_1)).

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

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [C_13,A_11,B_12] :
      ( k7_relat_1(k7_relat_1(C_13,A_11),B_12) = k7_relat_1(C_13,k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(C_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_154,plain,(
    ! [B_34,A_35] :
      ( k3_xboole_0(k1_relat_1(B_34),A_35) = k1_relat_1(k7_relat_1(B_34,A_35))
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_189,plain,(
    ! [B_40,A_41] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_40,A_41)),k1_relat_1(B_40))
      | ~ v1_relat_1(B_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_2])).

tff(c_16,plain,(
    ! [B_17,A_16] :
      ( k7_relat_1(B_17,A_16) = B_17
      | ~ r1_tarski(k1_relat_1(B_17),A_16)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_645,plain,(
    ! [B_67,A_68] :
      ( k7_relat_1(k7_relat_1(B_67,A_68),k1_relat_1(B_67)) = k7_relat_1(B_67,A_68)
      | ~ v1_relat_1(k7_relat_1(B_67,A_68))
      | ~ v1_relat_1(B_67) ) ),
    inference(resolution,[status(thm)],[c_189,c_16])).

tff(c_931,plain,(
    ! [C_76,A_77] :
      ( k7_relat_1(C_76,k3_xboole_0(A_77,k1_relat_1(C_76))) = k7_relat_1(C_76,A_77)
      | ~ v1_relat_1(k7_relat_1(C_76,A_77))
      | ~ v1_relat_1(C_76)
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_645])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [A_26,B_27] : k1_setfam_1(k2_tarski(A_26,B_27)) = k3_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_80,plain,(
    ! [B_28,A_29] : k1_setfam_1(k2_tarski(B_28,A_29)) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_65])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_8])).

tff(c_18,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_151,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_86,c_18])).

tff(c_991,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_931,c_151])).

tff(c_1035,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_991])).

tff(c_1040,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_1035])).

tff(c_1044,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1040])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.21/1.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.81  
% 3.21/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.21/1.81  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.21/1.81  
% 3.21/1.81  %Foreground sorts:
% 3.21/1.81  
% 3.21/1.81  
% 3.21/1.81  %Background operators:
% 3.21/1.81  
% 3.21/1.81  
% 3.21/1.81  %Foreground operators:
% 3.21/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.21/1.81  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.21/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.21/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.21/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.21/1.81  tff('#skF_2', type, '#skF_2': $i).
% 3.21/1.81  tff('#skF_1', type, '#skF_1': $i).
% 3.21/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.21/1.81  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.21/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.21/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.21/1.81  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.21/1.81  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.21/1.81  
% 3.33/1.82  tff(f_56, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t192_relat_1)).
% 3.33/1.82  tff(f_37, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.33/1.82  tff(f_41, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 3.33/1.82  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.33/1.82  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.33/1.82  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 3.33/1.82  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.33/1.82  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.33/1.82  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.82  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.33/1.82  tff(c_12, plain, (![C_13, A_11, B_12]: (k7_relat_1(k7_relat_1(C_13, A_11), B_12)=k7_relat_1(C_13, k3_xboole_0(A_11, B_12)) | ~v1_relat_1(C_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.33/1.82  tff(c_154, plain, (![B_34, A_35]: (k3_xboole_0(k1_relat_1(B_34), A_35)=k1_relat_1(k7_relat_1(B_34, A_35)) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.33/1.82  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.33/1.82  tff(c_189, plain, (![B_40, A_41]: (r1_tarski(k1_relat_1(k7_relat_1(B_40, A_41)), k1_relat_1(B_40)) | ~v1_relat_1(B_40))), inference(superposition, [status(thm), theory('equality')], [c_154, c_2])).
% 3.33/1.82  tff(c_16, plain, (![B_17, A_16]: (k7_relat_1(B_17, A_16)=B_17 | ~r1_tarski(k1_relat_1(B_17), A_16) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.33/1.82  tff(c_645, plain, (![B_67, A_68]: (k7_relat_1(k7_relat_1(B_67, A_68), k1_relat_1(B_67))=k7_relat_1(B_67, A_68) | ~v1_relat_1(k7_relat_1(B_67, A_68)) | ~v1_relat_1(B_67))), inference(resolution, [status(thm)], [c_189, c_16])).
% 3.33/1.82  tff(c_931, plain, (![C_76, A_77]: (k7_relat_1(C_76, k3_xboole_0(A_77, k1_relat_1(C_76)))=k7_relat_1(C_76, A_77) | ~v1_relat_1(k7_relat_1(C_76, A_77)) | ~v1_relat_1(C_76) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_12, c_645])).
% 3.33/1.82  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.33/1.82  tff(c_65, plain, (![A_26, B_27]: (k1_setfam_1(k2_tarski(A_26, B_27))=k3_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.82  tff(c_80, plain, (![B_28, A_29]: (k1_setfam_1(k2_tarski(B_28, A_29))=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_4, c_65])).
% 3.33/1.82  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.33/1.82  tff(c_86, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(superposition, [status(thm), theory('equality')], [c_80, c_8])).
% 3.33/1.82  tff(c_18, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.33/1.82  tff(c_151, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_86, c_18])).
% 3.33/1.82  tff(c_991, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_931, c_151])).
% 3.33/1.82  tff(c_1035, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_991])).
% 3.33/1.82  tff(c_1040, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_1035])).
% 3.33/1.82  tff(c_1044, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1040])).
% 3.33/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.33/1.82  
% 3.33/1.82  Inference rules
% 3.33/1.82  ----------------------
% 3.33/1.82  #Ref     : 0
% 3.33/1.82  #Sup     : 287
% 3.33/1.82  #Fact    : 0
% 3.33/1.82  #Define  : 0
% 3.33/1.82  #Split   : 0
% 3.33/1.82  #Chain   : 0
% 3.33/1.82  #Close   : 0
% 3.33/1.82  
% 3.33/1.82  Ordering : KBO
% 3.33/1.82  
% 3.33/1.82  Simplification rules
% 3.33/1.82  ----------------------
% 3.33/1.82  #Subsume      : 54
% 3.33/1.82  #Demod        : 10
% 3.33/1.82  #Tautology    : 62
% 3.33/1.82  #SimpNegUnit  : 0
% 3.33/1.82  #BackRed      : 0
% 3.33/1.82  
% 3.33/1.82  #Partial instantiations: 0
% 3.33/1.82  #Strategies tried      : 1
% 3.33/1.82  
% 3.33/1.82  Timing (in seconds)
% 3.33/1.82  ----------------------
% 3.37/1.82  Preprocessing        : 0.45
% 3.37/1.82  Parsing              : 0.24
% 3.37/1.82  CNF conversion       : 0.03
% 3.37/1.82  Main loop            : 0.45
% 3.37/1.82  Inferencing          : 0.18
% 3.37/1.82  Reduction            : 0.13
% 3.37/1.82  Demodulation         : 0.10
% 3.37/1.82  BG Simplification    : 0.03
% 3.37/1.82  Subsumption          : 0.08
% 3.37/1.82  Abstraction          : 0.03
% 3.37/1.82  MUC search           : 0.00
% 3.37/1.82  Cooper               : 0.00
% 3.37/1.83  Total                : 0.93
% 3.37/1.83  Index Insertion      : 0.00
% 3.37/1.83  Index Deletion       : 0.00
% 3.37/1.83  Index Matching       : 0.00
% 3.37/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
