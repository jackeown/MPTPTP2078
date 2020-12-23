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
% DateTime   : Thu Dec  3 09:59:49 EST 2020

% Result     : Theorem 14.64s
% Output     : CNFRefutation 14.64s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 102 expanded)
%              Number of leaves         :   21 (  43 expanded)
%              Depth                    :   18
%              Number of atoms          :   86 ( 151 expanded)
%              Number of equality atoms :   22 (  56 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t102_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k7_relat_1(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    ! [A_22,B_23] : k1_setfam_1(k2_tarski(A_22,B_23)) = k3_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(B_25,A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_85,plain,(
    ! [B_25,A_24] : k3_xboole_0(B_25,A_24) = k3_xboole_0(A_24,B_25) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_8])).

tff(c_150,plain,(
    ! [B_31,A_32] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_31,A_32)),A_32)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_153,plain,(
    ! [B_31,A_32] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1(B_31,A_32)),A_32) = k1_relat_1(k7_relat_1(B_31,A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_150,c_4])).

tff(c_155,plain,(
    ! [A_32,B_31] :
      ( k3_xboole_0(A_32,k1_relat_1(k7_relat_1(B_31,A_32))) = k1_relat_1(k7_relat_1(B_31,A_32))
      | ~ v1_relat_1(B_31) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_153])).

tff(c_18,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_136,plain,(
    ! [A_28,C_29,B_30] :
      ( r1_tarski(k3_xboole_0(A_28,C_29),B_30)
      | ~ r1_tarski(A_28,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_33,B_34,B_35] :
      ( r1_tarski(k3_xboole_0(A_33,B_34),B_35)
      | ~ r1_tarski(B_34,B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_136])).

tff(c_169,plain,(
    ! [A_33,B_34,B_35] :
      ( k3_xboole_0(k3_xboole_0(A_33,B_34),B_35) = k3_xboole_0(A_33,B_34)
      | ~ r1_tarski(B_34,B_35) ) ),
    inference(resolution,[status(thm)],[c_156,c_4])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_18,c_55])).

tff(c_12,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_13,A_12)),A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(k3_xboole_0(A_1,C_3),B_2)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_176,plain,(
    ! [A_39,C_40,B_41] :
      ( k3_xboole_0(k3_xboole_0(A_39,C_40),B_41) = k3_xboole_0(A_39,C_40)
      | ~ r1_tarski(A_39,B_41) ) ),
    inference(resolution,[status(thm)],[c_136,c_4])).

tff(c_350,plain,(
    ! [B_49,A_50,C_51] :
      ( k3_xboole_0(B_49,k3_xboole_0(A_50,C_51)) = k3_xboole_0(A_50,C_51)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_85])).

tff(c_512,plain,(
    ! [A_58,C_59,B_60,B_61] :
      ( r1_tarski(k3_xboole_0(A_58,C_59),B_60)
      | ~ r1_tarski(B_61,B_60)
      | ~ r1_tarski(A_58,B_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_2])).

tff(c_3067,plain,(
    ! [A_143,C_144,B_141,C_142,A_140] :
      ( r1_tarski(k3_xboole_0(A_140,C_144),B_141)
      | ~ r1_tarski(A_140,k3_xboole_0(A_143,C_142))
      | ~ r1_tarski(A_143,B_141) ) ),
    inference(resolution,[status(thm)],[c_2,c_512])).

tff(c_18307,plain,(
    ! [C_379,C_381,A_380,C_378,B_382,A_377] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(A_380,C_379),C_378),B_382)
      | ~ r1_tarski(A_377,B_382)
      | ~ r1_tarski(A_380,k3_xboole_0(A_377,C_381)) ) ),
    inference(resolution,[status(thm)],[c_2,c_3067])).

tff(c_18380,plain,(
    ! [A_383,C_384,C_385,C_386] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(A_383,C_384),C_385),'#skF_2')
      | ~ r1_tarski(A_383,k3_xboole_0('#skF_1',C_386)) ) ),
    inference(resolution,[status(thm)],[c_18,c_18307])).

tff(c_23263,plain,(
    ! [B_449,C_450,C_451,C_452] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(B_449,k3_xboole_0('#skF_1',C_450))),C_451),C_452),'#skF_2')
      | ~ v1_relat_1(B_449) ) ),
    inference(resolution,[status(thm)],[c_12,c_18380])).

tff(c_23575,plain,(
    ! [B_453,C_454,C_455] :
      ( r1_tarski(k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(B_453,'#skF_1')),C_454),C_455),'#skF_2')
      | ~ v1_relat_1(B_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_59,c_23263])).

tff(c_26826,plain,(
    ! [B_504,B_505,B_506] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(B_504,'#skF_1')),B_505),'#skF_2')
      | ~ v1_relat_1(B_504)
      | ~ r1_tarski(B_505,B_506) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_23575])).

tff(c_26908,plain,(
    ! [B_504] :
      ( r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(B_504,'#skF_1')),'#skF_1'),'#skF_2')
      | ~ v1_relat_1(B_504) ) ),
    inference(resolution,[status(thm)],[c_18,c_26826])).

tff(c_26951,plain,(
    ! [B_507] :
      ( r1_tarski(k3_xboole_0('#skF_1',k1_relat_1(k7_relat_1(B_507,'#skF_1'))),'#skF_2')
      | ~ v1_relat_1(B_507) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_26908])).

tff(c_27030,plain,(
    ! [B_508] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_508,'#skF_1')),'#skF_2')
      | ~ v1_relat_1(B_508)
      | ~ v1_relat_1(B_508) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_26951])).

tff(c_14,plain,(
    ! [B_15,A_14] :
      ( k7_relat_1(B_15,A_14) = B_15
      | ~ r1_tarski(k1_relat_1(B_15),A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_33187,plain,(
    ! [B_594] :
      ( k7_relat_1(k7_relat_1(B_594,'#skF_1'),'#skF_2') = k7_relat_1(B_594,'#skF_1')
      | ~ v1_relat_1(k7_relat_1(B_594,'#skF_1'))
      | ~ v1_relat_1(B_594) ) ),
    inference(resolution,[status(thm)],[c_27030,c_14])).

tff(c_33197,plain,(
    ! [A_595] :
      ( k7_relat_1(k7_relat_1(A_595,'#skF_1'),'#skF_2') = k7_relat_1(A_595,'#skF_1')
      | ~ v1_relat_1(A_595) ) ),
    inference(resolution,[status(thm)],[c_10,c_33187])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_3','#skF_1'),'#skF_2') != k7_relat_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_33249,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_33197,c_16])).

tff(c_33265,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_33249])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:52:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.64/7.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/7.31  
% 14.64/7.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/7.31  %$ r1_tarski > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 14.64/7.31  
% 14.64/7.31  %Foreground sorts:
% 14.64/7.31  
% 14.64/7.31  
% 14.64/7.31  %Background operators:
% 14.64/7.31  
% 14.64/7.31  
% 14.64/7.31  %Foreground operators:
% 14.64/7.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.64/7.31  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 14.64/7.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 14.64/7.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.64/7.31  tff('#skF_2', type, '#skF_2': $i).
% 14.64/7.31  tff('#skF_3', type, '#skF_3': $i).
% 14.64/7.31  tff('#skF_1', type, '#skF_1': $i).
% 14.64/7.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.64/7.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.64/7.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.64/7.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.64/7.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 14.64/7.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 14.64/7.31  
% 14.64/7.32  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t102_relat_1)).
% 14.64/7.32  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 14.64/7.32  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.64/7.32  tff(f_37, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 14.64/7.32  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 14.64/7.32  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 14.64/7.32  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 14.64/7.32  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 14.64/7.32  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.64/7.32  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k7_relat_1(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.64/7.32  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.64/7.32  tff(c_60, plain, (![A_22, B_23]: (k1_setfam_1(k2_tarski(A_22, B_23))=k3_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.64/7.32  tff(c_79, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(B_25, A_24))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 14.64/7.32  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.64/7.32  tff(c_85, plain, (![B_25, A_24]: (k3_xboole_0(B_25, A_24)=k3_xboole_0(A_24, B_25))), inference(superposition, [status(thm), theory('equality')], [c_79, c_8])).
% 14.64/7.32  tff(c_150, plain, (![B_31, A_32]: (r1_tarski(k1_relat_1(k7_relat_1(B_31, A_32)), A_32) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.64/7.32  tff(c_4, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.64/7.32  tff(c_153, plain, (![B_31, A_32]: (k3_xboole_0(k1_relat_1(k7_relat_1(B_31, A_32)), A_32)=k1_relat_1(k7_relat_1(B_31, A_32)) | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_150, c_4])).
% 14.64/7.32  tff(c_155, plain, (![A_32, B_31]: (k3_xboole_0(A_32, k1_relat_1(k7_relat_1(B_31, A_32)))=k1_relat_1(k7_relat_1(B_31, A_32)) | ~v1_relat_1(B_31))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_153])).
% 14.64/7.32  tff(c_18, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.64/7.32  tff(c_136, plain, (![A_28, C_29, B_30]: (r1_tarski(k3_xboole_0(A_28, C_29), B_30) | ~r1_tarski(A_28, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.64/7.32  tff(c_156, plain, (![A_33, B_34, B_35]: (r1_tarski(k3_xboole_0(A_33, B_34), B_35) | ~r1_tarski(B_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_85, c_136])).
% 14.64/7.32  tff(c_169, plain, (![A_33, B_34, B_35]: (k3_xboole_0(k3_xboole_0(A_33, B_34), B_35)=k3_xboole_0(A_33, B_34) | ~r1_tarski(B_34, B_35))), inference(resolution, [status(thm)], [c_156, c_4])).
% 14.64/7.32  tff(c_55, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.64/7.32  tff(c_59, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_18, c_55])).
% 14.64/7.32  tff(c_12, plain, (![B_13, A_12]: (r1_tarski(k1_relat_1(k7_relat_1(B_13, A_12)), A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.64/7.32  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(k3_xboole_0(A_1, C_3), B_2) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 14.64/7.32  tff(c_176, plain, (![A_39, C_40, B_41]: (k3_xboole_0(k3_xboole_0(A_39, C_40), B_41)=k3_xboole_0(A_39, C_40) | ~r1_tarski(A_39, B_41))), inference(resolution, [status(thm)], [c_136, c_4])).
% 14.64/7.32  tff(c_350, plain, (![B_49, A_50, C_51]: (k3_xboole_0(B_49, k3_xboole_0(A_50, C_51))=k3_xboole_0(A_50, C_51) | ~r1_tarski(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_176, c_85])).
% 14.64/7.32  tff(c_512, plain, (![A_58, C_59, B_60, B_61]: (r1_tarski(k3_xboole_0(A_58, C_59), B_60) | ~r1_tarski(B_61, B_60) | ~r1_tarski(A_58, B_61))), inference(superposition, [status(thm), theory('equality')], [c_350, c_2])).
% 14.64/7.32  tff(c_3067, plain, (![A_143, C_144, B_141, C_142, A_140]: (r1_tarski(k3_xboole_0(A_140, C_144), B_141) | ~r1_tarski(A_140, k3_xboole_0(A_143, C_142)) | ~r1_tarski(A_143, B_141))), inference(resolution, [status(thm)], [c_2, c_512])).
% 14.64/7.32  tff(c_18307, plain, (![C_379, C_381, A_380, C_378, B_382, A_377]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_380, C_379), C_378), B_382) | ~r1_tarski(A_377, B_382) | ~r1_tarski(A_380, k3_xboole_0(A_377, C_381)))), inference(resolution, [status(thm)], [c_2, c_3067])).
% 14.64/7.32  tff(c_18380, plain, (![A_383, C_384, C_385, C_386]: (r1_tarski(k3_xboole_0(k3_xboole_0(A_383, C_384), C_385), '#skF_2') | ~r1_tarski(A_383, k3_xboole_0('#skF_1', C_386)))), inference(resolution, [status(thm)], [c_18, c_18307])).
% 14.64/7.32  tff(c_23263, plain, (![B_449, C_450, C_451, C_452]: (r1_tarski(k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(B_449, k3_xboole_0('#skF_1', C_450))), C_451), C_452), '#skF_2') | ~v1_relat_1(B_449))), inference(resolution, [status(thm)], [c_12, c_18380])).
% 14.64/7.32  tff(c_23575, plain, (![B_453, C_454, C_455]: (r1_tarski(k3_xboole_0(k3_xboole_0(k1_relat_1(k7_relat_1(B_453, '#skF_1')), C_454), C_455), '#skF_2') | ~v1_relat_1(B_453))), inference(superposition, [status(thm), theory('equality')], [c_59, c_23263])).
% 14.64/7.32  tff(c_26826, plain, (![B_504, B_505, B_506]: (r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(B_504, '#skF_1')), B_505), '#skF_2') | ~v1_relat_1(B_504) | ~r1_tarski(B_505, B_506))), inference(superposition, [status(thm), theory('equality')], [c_169, c_23575])).
% 14.64/7.32  tff(c_26908, plain, (![B_504]: (r1_tarski(k3_xboole_0(k1_relat_1(k7_relat_1(B_504, '#skF_1')), '#skF_1'), '#skF_2') | ~v1_relat_1(B_504))), inference(resolution, [status(thm)], [c_18, c_26826])).
% 14.64/7.32  tff(c_26951, plain, (![B_507]: (r1_tarski(k3_xboole_0('#skF_1', k1_relat_1(k7_relat_1(B_507, '#skF_1'))), '#skF_2') | ~v1_relat_1(B_507))), inference(demodulation, [status(thm), theory('equality')], [c_85, c_26908])).
% 14.64/7.32  tff(c_27030, plain, (![B_508]: (r1_tarski(k1_relat_1(k7_relat_1(B_508, '#skF_1')), '#skF_2') | ~v1_relat_1(B_508) | ~v1_relat_1(B_508))), inference(superposition, [status(thm), theory('equality')], [c_155, c_26951])).
% 14.64/7.32  tff(c_14, plain, (![B_15, A_14]: (k7_relat_1(B_15, A_14)=B_15 | ~r1_tarski(k1_relat_1(B_15), A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.64/7.32  tff(c_33187, plain, (![B_594]: (k7_relat_1(k7_relat_1(B_594, '#skF_1'), '#skF_2')=k7_relat_1(B_594, '#skF_1') | ~v1_relat_1(k7_relat_1(B_594, '#skF_1')) | ~v1_relat_1(B_594))), inference(resolution, [status(thm)], [c_27030, c_14])).
% 14.64/7.32  tff(c_33197, plain, (![A_595]: (k7_relat_1(k7_relat_1(A_595, '#skF_1'), '#skF_2')=k7_relat_1(A_595, '#skF_1') | ~v1_relat_1(A_595))), inference(resolution, [status(thm)], [c_10, c_33187])).
% 14.64/7.32  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_3', '#skF_1'), '#skF_2')!=k7_relat_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 14.64/7.32  tff(c_33249, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_33197, c_16])).
% 14.64/7.32  tff(c_33265, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_33249])).
% 14.64/7.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 14.64/7.32  
% 14.64/7.32  Inference rules
% 14.64/7.32  ----------------------
% 14.64/7.32  #Ref     : 0
% 14.64/7.32  #Sup     : 9988
% 14.64/7.32  #Fact    : 0
% 14.64/7.32  #Define  : 0
% 14.64/7.32  #Split   : 2
% 14.64/7.32  #Chain   : 0
% 14.64/7.32  #Close   : 0
% 14.64/7.32  
% 14.64/7.32  Ordering : KBO
% 14.64/7.32  
% 14.64/7.32  Simplification rules
% 14.64/7.32  ----------------------
% 14.64/7.32  #Subsume      : 3799
% 14.64/7.32  #Demod        : 1005
% 14.64/7.32  #Tautology    : 283
% 14.64/7.32  #SimpNegUnit  : 0
% 14.64/7.32  #BackRed      : 0
% 14.64/7.32  
% 14.64/7.32  #Partial instantiations: 0
% 14.64/7.32  #Strategies tried      : 1
% 14.64/7.32  
% 14.64/7.32  Timing (in seconds)
% 14.64/7.32  ----------------------
% 14.64/7.33  Preprocessing        : 0.26
% 14.64/7.33  Parsing              : 0.14
% 14.64/7.33  CNF conversion       : 0.02
% 14.64/7.33  Main loop            : 6.30
% 14.64/7.33  Inferencing          : 1.08
% 14.64/7.33  Reduction            : 1.52
% 14.64/7.33  Demodulation         : 1.22
% 14.64/7.33  BG Simplification    : 0.16
% 14.64/7.33  Subsumption          : 3.24
% 14.64/7.33  Abstraction          : 0.21
% 14.64/7.33  MUC search           : 0.00
% 14.64/7.33  Cooper               : 0.00
% 14.64/7.33  Total                : 6.59
% 14.64/7.33  Index Insertion      : 0.00
% 14.64/7.33  Index Deletion       : 0.00
% 14.64/7.33  Index Matching       : 0.00
% 14.64/7.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
