%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:36 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   26 (  44 expanded)
%              Depth                    :    8
%              Number of atoms          :   65 ( 122 expanded)
%              Number of equality atoms :   38 (  69 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(c_189,plain,(
    ! [A_39,B_40] : k4_xboole_0(A_39,k4_xboole_0(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_26,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_112,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_100])).

tff(c_222,plain,(
    ! [B_41] : k3_xboole_0(k1_xboole_0,B_41) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_189,c_112])).

tff(c_30,plain,(
    ! [B_15,A_14] : k2_tarski(B_15,A_14) = k2_tarski(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_84,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_124,plain,(
    ! [A_31,B_32] : k1_setfam_1(k2_tarski(A_31,B_32)) = k3_xboole_0(B_32,A_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_84])).

tff(c_32,plain,(
    ! [A_16,B_17] : k1_setfam_1(k2_tarski(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_130,plain,(
    ! [B_32,A_31] : k3_xboole_0(B_32,A_31) = k3_xboole_0(A_31,B_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_32])).

tff(c_230,plain,(
    ! [B_41] : k3_xboole_0(B_41,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_130])).

tff(c_20,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1063,plain,(
    ! [A_95,B_96,C_97] :
      ( r2_hidden('#skF_1'(A_95,B_96,C_97),A_95)
      | r2_hidden('#skF_2'(A_95,B_96,C_97),C_97)
      | k4_xboole_0(A_95,B_96) = C_97 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1154,plain,(
    ! [A_95,C_97] :
      ( r2_hidden('#skF_2'(A_95,A_95,C_97),C_97)
      | k4_xboole_0(A_95,A_95) = C_97 ) ),
    inference(resolution,[status(thm)],[c_1063,c_16])).

tff(c_1175,plain,(
    ! [A_98,C_99] :
      ( r2_hidden('#skF_2'(A_98,A_98,C_99),C_99)
      | k4_xboole_0(A_98,A_98) = C_99 ) ),
    inference(resolution,[status(thm)],[c_1063,c_16])).

tff(c_304,plain,(
    ! [D_43,B_44,A_45] :
      ( ~ r2_hidden(D_43,B_44)
      | ~ r2_hidden(D_43,k4_xboole_0(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_310,plain,(
    ! [D_43,A_11] :
      ( ~ r2_hidden(D_43,A_11)
      | ~ r2_hidden(D_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_304])).

tff(c_1282,plain,(
    ! [A_102,C_103] :
      ( ~ r2_hidden('#skF_2'(A_102,A_102,C_103),k1_xboole_0)
      | k4_xboole_0(A_102,A_102) = C_103 ) ),
    inference(resolution,[status(thm)],[c_1175,c_310])).

tff(c_1306,plain,(
    ! [A_106] : k4_xboole_0(A_106,A_106) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1154,c_1282])).

tff(c_28,plain,(
    ! [A_12,B_13] : k4_xboole_0(A_12,k4_xboole_0(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_465,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k3_xboole_0(A_65,k4_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_189])).

tff(c_477,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k3_xboole_0(A_65,k4_xboole_0(A_65,B_66))) = k3_xboole_0(A_65,k3_xboole_0(A_65,B_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_28])).

tff(c_1314,plain,(
    ! [A_106] : k4_xboole_0(A_106,k3_xboole_0(A_106,k1_xboole_0)) = k3_xboole_0(A_106,k3_xboole_0(A_106,A_106)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1306,c_477])).

tff(c_1344,plain,(
    ! [A_106] : k4_xboole_0(A_106,k1_xboole_0) = A_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_230,c_20,c_20,c_1314])).

tff(c_40,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_316,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(k1_relat_1(B_48),A_49) = k1_relat_1(k7_relat_1(B_48,A_49))
      | ~ v1_relat_1(B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_748,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(A_77,k1_relat_1(B_78)) = k1_relat_1(k7_relat_1(B_78,A_77))
      | ~ v1_relat_1(B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_316])).

tff(c_38,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_111,plain,(
    k4_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_218,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_111,c_189])).

tff(c_770,plain,
    ( k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k4_xboole_0('#skF_3',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_748,c_218])).

tff(c_819,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) = k4_xboole_0('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_770])).

tff(c_36,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_824,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_819,c_36])).

tff(c_1358,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_824])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:56:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.47  %$ r2_hidden > r1_tarski > v1_relat_1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.15/1.47  
% 3.15/1.47  %Foreground sorts:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Background operators:
% 3.15/1.47  
% 3.15/1.47  
% 3.15/1.47  %Foreground operators:
% 3.15/1.47  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.47  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.15/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.47  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.15/1.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.15/1.47  
% 3.15/1.49  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.15/1.49  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.49  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.15/1.49  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.15/1.49  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.15/1.49  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.15/1.49  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.15/1.49  tff(f_60, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 3.15/1.49  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.15/1.49  tff(c_189, plain, (![A_39, B_40]: (k4_xboole_0(A_39, k4_xboole_0(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.49  tff(c_26, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.49  tff(c_100, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.49  tff(c_112, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_100])).
% 3.15/1.49  tff(c_222, plain, (![B_41]: (k3_xboole_0(k1_xboole_0, B_41)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_189, c_112])).
% 3.15/1.49  tff(c_30, plain, (![B_15, A_14]: (k2_tarski(B_15, A_14)=k2_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.49  tff(c_84, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.49  tff(c_124, plain, (![A_31, B_32]: (k1_setfam_1(k2_tarski(A_31, B_32))=k3_xboole_0(B_32, A_31))), inference(superposition, [status(thm), theory('equality')], [c_30, c_84])).
% 3.15/1.49  tff(c_32, plain, (![A_16, B_17]: (k1_setfam_1(k2_tarski(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.15/1.49  tff(c_130, plain, (![B_32, A_31]: (k3_xboole_0(B_32, A_31)=k3_xboole_0(A_31, B_32))), inference(superposition, [status(thm), theory('equality')], [c_124, c_32])).
% 3.15/1.49  tff(c_230, plain, (![B_41]: (k3_xboole_0(B_41, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_222, c_130])).
% 3.15/1.49  tff(c_20, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.49  tff(c_1063, plain, (![A_95, B_96, C_97]: (r2_hidden('#skF_1'(A_95, B_96, C_97), A_95) | r2_hidden('#skF_2'(A_95, B_96, C_97), C_97) | k4_xboole_0(A_95, B_96)=C_97)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.49  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.49  tff(c_1154, plain, (![A_95, C_97]: (r2_hidden('#skF_2'(A_95, A_95, C_97), C_97) | k4_xboole_0(A_95, A_95)=C_97)), inference(resolution, [status(thm)], [c_1063, c_16])).
% 3.15/1.49  tff(c_1175, plain, (![A_98, C_99]: (r2_hidden('#skF_2'(A_98, A_98, C_99), C_99) | k4_xboole_0(A_98, A_98)=C_99)), inference(resolution, [status(thm)], [c_1063, c_16])).
% 3.15/1.49  tff(c_304, plain, (![D_43, B_44, A_45]: (~r2_hidden(D_43, B_44) | ~r2_hidden(D_43, k4_xboole_0(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.49  tff(c_310, plain, (![D_43, A_11]: (~r2_hidden(D_43, A_11) | ~r2_hidden(D_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_112, c_304])).
% 3.15/1.49  tff(c_1282, plain, (![A_102, C_103]: (~r2_hidden('#skF_2'(A_102, A_102, C_103), k1_xboole_0) | k4_xboole_0(A_102, A_102)=C_103)), inference(resolution, [status(thm)], [c_1175, c_310])).
% 3.15/1.49  tff(c_1306, plain, (![A_106]: (k4_xboole_0(A_106, A_106)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1154, c_1282])).
% 3.15/1.49  tff(c_28, plain, (![A_12, B_13]: (k4_xboole_0(A_12, k4_xboole_0(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.49  tff(c_465, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k3_xboole_0(A_65, k4_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_189])).
% 3.15/1.49  tff(c_477, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_xboole_0(A_65, k4_xboole_0(A_65, B_66)))=k3_xboole_0(A_65, k3_xboole_0(A_65, B_66)))), inference(superposition, [status(thm), theory('equality')], [c_465, c_28])).
% 3.15/1.49  tff(c_1314, plain, (![A_106]: (k4_xboole_0(A_106, k3_xboole_0(A_106, k1_xboole_0))=k3_xboole_0(A_106, k3_xboole_0(A_106, A_106)))), inference(superposition, [status(thm), theory('equality')], [c_1306, c_477])).
% 3.15/1.49  tff(c_1344, plain, (![A_106]: (k4_xboole_0(A_106, k1_xboole_0)=A_106)), inference(demodulation, [status(thm), theory('equality')], [c_230, c_20, c_20, c_1314])).
% 3.15/1.49  tff(c_40, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_316, plain, (![B_48, A_49]: (k3_xboole_0(k1_relat_1(B_48), A_49)=k1_relat_1(k7_relat_1(B_48, A_49)) | ~v1_relat_1(B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.15/1.49  tff(c_748, plain, (![A_77, B_78]: (k3_xboole_0(A_77, k1_relat_1(B_78))=k1_relat_1(k7_relat_1(B_78, A_77)) | ~v1_relat_1(B_78))), inference(superposition, [status(thm), theory('equality')], [c_130, c_316])).
% 3.15/1.49  tff(c_38, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_111, plain, (k4_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_100])).
% 3.15/1.49  tff(c_218, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_111, c_189])).
% 3.15/1.49  tff(c_770, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_748, c_218])).
% 3.15/1.49  tff(c_819, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))=k4_xboole_0('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_770])).
% 3.15/1.49  tff(c_36, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.15/1.49  tff(c_824, plain, (k4_xboole_0('#skF_3', k1_xboole_0)!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_819, c_36])).
% 3.15/1.49  tff(c_1358, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1344, c_824])).
% 3.15/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.49  
% 3.15/1.49  Inference rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Ref     : 0
% 3.15/1.49  #Sup     : 322
% 3.15/1.49  #Fact    : 0
% 3.15/1.49  #Define  : 0
% 3.15/1.49  #Split   : 0
% 3.15/1.49  #Chain   : 0
% 3.15/1.49  #Close   : 0
% 3.15/1.49  
% 3.15/1.49  Ordering : KBO
% 3.15/1.49  
% 3.15/1.49  Simplification rules
% 3.15/1.49  ----------------------
% 3.15/1.49  #Subsume      : 50
% 3.15/1.49  #Demod        : 134
% 3.15/1.49  #Tautology    : 131
% 3.15/1.49  #SimpNegUnit  : 0
% 3.15/1.49  #BackRed      : 10
% 3.15/1.49  
% 3.15/1.49  #Partial instantiations: 0
% 3.15/1.49  #Strategies tried      : 1
% 3.15/1.49  
% 3.15/1.49  Timing (in seconds)
% 3.15/1.49  ----------------------
% 3.15/1.49  Preprocessing        : 0.30
% 3.15/1.49  Parsing              : 0.16
% 3.15/1.49  CNF conversion       : 0.02
% 3.15/1.49  Main loop            : 0.43
% 3.15/1.49  Inferencing          : 0.15
% 3.15/1.49  Reduction            : 0.14
% 3.15/1.49  Demodulation         : 0.11
% 3.15/1.49  BG Simplification    : 0.02
% 3.15/1.49  Subsumption          : 0.08
% 3.15/1.49  Abstraction          : 0.02
% 3.15/1.49  MUC search           : 0.00
% 3.15/1.49  Cooper               : 0.00
% 3.15/1.49  Total                : 0.75
% 3.15/1.49  Index Insertion      : 0.00
% 3.15/1.49  Index Deletion       : 0.00
% 3.15/1.49  Index Matching       : 0.00
% 3.15/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
