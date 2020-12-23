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
% DateTime   : Thu Dec  3 10:17:27 EST 2020

% Result     : Theorem 2.88s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 129 expanded)
%              Number of leaves         :   28 (  58 expanded)
%              Depth                    :   18
%              Number of atoms          :   81 ( 207 expanded)
%              Number of equality atoms :   31 (  76 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_91,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_36,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_38,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_28,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_85,plain,(
    ! [B_42,A_43] :
      ( r1_tarski(k10_relat_1(B_42,A_43),k1_relat_1(B_42))
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_88,plain,(
    ! [A_16,A_43] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_16),A_43),A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_85])).

tff(c_90,plain,(
    ! [A_16,A_43] : r1_tarski(k10_relat_1(k6_relat_1(A_16),A_43),A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_88])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_195,plain,(
    ! [B_61,A_62] :
      ( k7_relat_1(B_61,A_62) = B_61
      | ~ r1_tarski(k1_relat_1(B_61),A_62)
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_219,plain,(
    ! [B_66] :
      ( k7_relat_1(B_66,k1_relat_1(B_66)) = B_66
      | ~ v1_relat_1(B_66) ) ),
    inference(resolution,[status(thm)],[c_6,c_195])).

tff(c_237,plain,(
    ! [A_16] :
      ( k7_relat_1(k6_relat_1(A_16),A_16) = k6_relat_1(A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_243,plain,(
    ! [A_67] : k7_relat_1(k6_relat_1(A_67),A_67) = k6_relat_1(A_67) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_237])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( k2_relat_1(k7_relat_1(B_13,A_12)) = k9_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_249,plain,(
    ! [A_67] :
      ( k9_relat_1(k6_relat_1(A_67),A_67) = k2_relat_1(k6_relat_1(A_67))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_16])).

tff(c_261,plain,(
    ! [A_67] : k9_relat_1(k6_relat_1(A_67),A_67) = A_67 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_249])).

tff(c_458,plain,(
    ! [A_81,B_82] :
      ( r1_tarski(A_81,k10_relat_1(B_82,k9_relat_1(B_82,A_81)))
      | ~ r1_tarski(A_81,k1_relat_1(B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_482,plain,(
    ! [A_67] :
      ( r1_tarski(A_67,k10_relat_1(k6_relat_1(A_67),A_67))
      | ~ r1_tarski(A_67,k1_relat_1(k6_relat_1(A_67)))
      | ~ v1_relat_1(k6_relat_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_458])).

tff(c_496,plain,(
    ! [A_83] : r1_tarski(A_83,k10_relat_1(k6_relat_1(A_83),A_83)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_20,c_482])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_510,plain,(
    ! [A_83] :
      ( k10_relat_1(k6_relat_1(A_83),A_83) = A_83
      | ~ r1_tarski(k10_relat_1(k6_relat_1(A_83),A_83),A_83) ) ),
    inference(resolution,[status(thm)],[c_496,c_2])).

tff(c_520,plain,(
    ! [A_83] : k10_relat_1(k6_relat_1(A_83),A_83) = A_83 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_510])).

tff(c_201,plain,(
    ! [A_16,A_62] :
      ( k7_relat_1(k6_relat_1(A_16),A_62) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_62)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_195])).

tff(c_208,plain,(
    ! [A_16,A_62] :
      ( k7_relat_1(k6_relat_1(A_16),A_62) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_201])).

tff(c_523,plain,(
    ! [A_84] : k10_relat_1(k6_relat_1(A_84),A_84) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_510])).

tff(c_32,plain,(
    ! [A_22,C_24,B_23] :
      ( k3_xboole_0(A_22,k10_relat_1(C_24,B_23)) = k10_relat_1(k7_relat_1(C_24,A_22),B_23)
      | ~ v1_relat_1(C_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_532,plain,(
    ! [A_84,A_22] :
      ( k10_relat_1(k7_relat_1(k6_relat_1(A_84),A_22),A_84) = k3_xboole_0(A_22,A_84)
      | ~ v1_relat_1(k6_relat_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_32])).

tff(c_665,plain,(
    ! [A_89,A_90] : k10_relat_1(k7_relat_1(k6_relat_1(A_89),A_90),A_89) = k3_xboole_0(A_90,A_89) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_532])).

tff(c_687,plain,(
    ! [A_62,A_16] :
      ( k3_xboole_0(A_62,A_16) = k10_relat_1(k6_relat_1(A_16),A_16)
      | ~ r1_tarski(A_16,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_665])).

tff(c_748,plain,(
    ! [A_94,A_95] :
      ( k3_xboole_0(A_94,A_95) = A_95
      | ~ r1_tarski(A_95,A_94) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_687])).

tff(c_791,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_748])).

tff(c_878,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_32])).

tff(c_885,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_878])).

tff(c_887,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_885])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:44:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.88/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.52  
% 2.88/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.52  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.88/1.52  
% 2.88/1.52  %Foreground sorts:
% 2.88/1.52  
% 2.88/1.52  
% 2.88/1.52  %Background operators:
% 2.88/1.52  
% 2.88/1.52  
% 2.88/1.52  %Foreground operators:
% 2.88/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.88/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.88/1.52  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.88/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.88/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.88/1.52  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.88/1.52  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.88/1.52  tff('#skF_2', type, '#skF_2': $i).
% 2.88/1.52  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.88/1.52  tff('#skF_3', type, '#skF_3': $i).
% 2.88/1.52  tff('#skF_1', type, '#skF_1': $i).
% 2.88/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.88/1.52  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.88/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.88/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.88/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.88/1.52  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.88/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.88/1.52  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.88/1.52  
% 2.88/1.53  tff(f_91, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_funct_2)).
% 2.88/1.53  tff(f_71, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 2.88/1.53  tff(f_57, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.88/1.53  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 2.88/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.88/1.53  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t97_relat_1)).
% 2.88/1.53  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 2.88/1.53  tff(f_81, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 2.88/1.53  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 2.88/1.53  tff(c_36, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.53  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.53  tff(c_38, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.88/1.53  tff(c_28, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.88/1.53  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.53  tff(c_85, plain, (![B_42, A_43]: (r1_tarski(k10_relat_1(B_42, A_43), k1_relat_1(B_42)) | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.53  tff(c_88, plain, (![A_16, A_43]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_43), A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_85])).
% 2.88/1.53  tff(c_90, plain, (![A_16, A_43]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_43), A_16))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_88])).
% 2.88/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.53  tff(c_22, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.88/1.53  tff(c_195, plain, (![B_61, A_62]: (k7_relat_1(B_61, A_62)=B_61 | ~r1_tarski(k1_relat_1(B_61), A_62) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.88/1.53  tff(c_219, plain, (![B_66]: (k7_relat_1(B_66, k1_relat_1(B_66))=B_66 | ~v1_relat_1(B_66))), inference(resolution, [status(thm)], [c_6, c_195])).
% 2.88/1.53  tff(c_237, plain, (![A_16]: (k7_relat_1(k6_relat_1(A_16), A_16)=k6_relat_1(A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_219])).
% 2.88/1.53  tff(c_243, plain, (![A_67]: (k7_relat_1(k6_relat_1(A_67), A_67)=k6_relat_1(A_67))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_237])).
% 2.88/1.53  tff(c_16, plain, (![B_13, A_12]: (k2_relat_1(k7_relat_1(B_13, A_12))=k9_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.88/1.53  tff(c_249, plain, (![A_67]: (k9_relat_1(k6_relat_1(A_67), A_67)=k2_relat_1(k6_relat_1(A_67)) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_243, c_16])).
% 2.88/1.53  tff(c_261, plain, (![A_67]: (k9_relat_1(k6_relat_1(A_67), A_67)=A_67)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_249])).
% 2.88/1.53  tff(c_458, plain, (![A_81, B_82]: (r1_tarski(A_81, k10_relat_1(B_82, k9_relat_1(B_82, A_81))) | ~r1_tarski(A_81, k1_relat_1(B_82)) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.88/1.53  tff(c_482, plain, (![A_67]: (r1_tarski(A_67, k10_relat_1(k6_relat_1(A_67), A_67)) | ~r1_tarski(A_67, k1_relat_1(k6_relat_1(A_67))) | ~v1_relat_1(k6_relat_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_261, c_458])).
% 2.88/1.53  tff(c_496, plain, (![A_83]: (r1_tarski(A_83, k10_relat_1(k6_relat_1(A_83), A_83)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_20, c_482])).
% 2.88/1.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.88/1.53  tff(c_510, plain, (![A_83]: (k10_relat_1(k6_relat_1(A_83), A_83)=A_83 | ~r1_tarski(k10_relat_1(k6_relat_1(A_83), A_83), A_83))), inference(resolution, [status(thm)], [c_496, c_2])).
% 2.88/1.53  tff(c_520, plain, (![A_83]: (k10_relat_1(k6_relat_1(A_83), A_83)=A_83)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_510])).
% 2.88/1.53  tff(c_201, plain, (![A_16, A_62]: (k7_relat_1(k6_relat_1(A_16), A_62)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_62) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_195])).
% 2.88/1.53  tff(c_208, plain, (![A_16, A_62]: (k7_relat_1(k6_relat_1(A_16), A_62)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_62))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_201])).
% 2.88/1.53  tff(c_523, plain, (![A_84]: (k10_relat_1(k6_relat_1(A_84), A_84)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_90, c_510])).
% 2.88/1.53  tff(c_32, plain, (![A_22, C_24, B_23]: (k3_xboole_0(A_22, k10_relat_1(C_24, B_23))=k10_relat_1(k7_relat_1(C_24, A_22), B_23) | ~v1_relat_1(C_24))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.88/1.53  tff(c_532, plain, (![A_84, A_22]: (k10_relat_1(k7_relat_1(k6_relat_1(A_84), A_22), A_84)=k3_xboole_0(A_22, A_84) | ~v1_relat_1(k6_relat_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_523, c_32])).
% 2.88/1.53  tff(c_665, plain, (![A_89, A_90]: (k10_relat_1(k7_relat_1(k6_relat_1(A_89), A_90), A_89)=k3_xboole_0(A_90, A_89))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_532])).
% 2.88/1.53  tff(c_687, plain, (![A_62, A_16]: (k3_xboole_0(A_62, A_16)=k10_relat_1(k6_relat_1(A_16), A_16) | ~r1_tarski(A_16, A_62))), inference(superposition, [status(thm), theory('equality')], [c_208, c_665])).
% 2.88/1.53  tff(c_748, plain, (![A_94, A_95]: (k3_xboole_0(A_94, A_95)=A_95 | ~r1_tarski(A_95, A_94))), inference(demodulation, [status(thm), theory('equality')], [c_520, c_687])).
% 2.88/1.53  tff(c_791, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_748])).
% 2.88/1.53  tff(c_878, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_791, c_32])).
% 2.88/1.53  tff(c_885, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_878])).
% 2.88/1.53  tff(c_887, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_885])).
% 2.88/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.88/1.53  
% 2.88/1.53  Inference rules
% 2.88/1.53  ----------------------
% 2.88/1.53  #Ref     : 0
% 2.88/1.53  #Sup     : 181
% 2.88/1.53  #Fact    : 0
% 2.88/1.53  #Define  : 0
% 2.88/1.53  #Split   : 1
% 2.88/1.53  #Chain   : 0
% 2.88/1.53  #Close   : 0
% 2.88/1.53  
% 2.88/1.53  Ordering : KBO
% 2.88/1.53  
% 2.88/1.53  Simplification rules
% 2.88/1.53  ----------------------
% 2.88/1.53  #Subsume      : 7
% 2.88/1.53  #Demod        : 153
% 2.88/1.53  #Tautology    : 96
% 2.88/1.53  #SimpNegUnit  : 1
% 2.88/1.53  #BackRed      : 1
% 2.88/1.53  
% 2.88/1.53  #Partial instantiations: 0
% 2.88/1.53  #Strategies tried      : 1
% 2.88/1.53  
% 2.88/1.53  Timing (in seconds)
% 2.88/1.53  ----------------------
% 2.88/1.54  Preprocessing        : 0.40
% 2.88/1.54  Parsing              : 0.23
% 2.88/1.54  CNF conversion       : 0.02
% 2.88/1.54  Main loop            : 0.35
% 2.88/1.54  Inferencing          : 0.13
% 2.88/1.54  Reduction            : 0.12
% 2.88/1.54  Demodulation         : 0.09
% 2.88/1.54  BG Simplification    : 0.02
% 2.88/1.54  Subsumption          : 0.07
% 2.88/1.54  Abstraction          : 0.02
% 2.88/1.54  MUC search           : 0.00
% 2.88/1.54  Cooper               : 0.00
% 2.88/1.54  Total                : 0.79
% 2.88/1.54  Index Insertion      : 0.00
% 2.88/1.54  Index Deletion       : 0.00
% 2.88/1.54  Index Matching       : 0.00
% 2.88/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
