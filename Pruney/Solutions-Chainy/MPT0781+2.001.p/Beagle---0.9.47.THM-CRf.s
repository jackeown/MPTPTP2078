%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:44 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   52 (  59 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  74 expanded)
%              Number of equality atoms :   33 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k2_wellord1(A,k3_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_wellord1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_36,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k8_relat_1(A,k7_relat_1(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_wellord1)).

tff(c_24,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_9] :
      ( k2_xboole_0(k1_relat_1(A_9),k2_relat_1(A_9)) = k3_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    ! [A_22,B_23] : k3_tarski(k2_tarski(A_22,B_23)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_90,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(B_27,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_70])).

tff(c_12,plain,(
    ! [A_7,B_8] : k3_tarski(k2_tarski(A_7,B_8)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_125,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_8,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_164,plain,(
    ! [B_31,A_32] : k4_xboole_0(B_31,k2_xboole_0(A_32,B_31)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_8])).

tff(c_180,plain,(
    ! [A_9] :
      ( k4_xboole_0(k2_relat_1(A_9),k3_relat_1(A_9)) = k1_xboole_0
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_164])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_192,plain,(
    ! [A_33,B_34] :
      ( k8_relat_1(A_33,B_34) = B_34
      | ~ r1_tarski(k2_relat_1(B_34),A_33)
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_231,plain,(
    ! [B_41,B_42] :
      ( k8_relat_1(B_41,B_42) = B_42
      | ~ v1_relat_1(B_42)
      | k4_xboole_0(k2_relat_1(B_42),B_41) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_192])).

tff(c_243,plain,(
    ! [A_9] :
      ( k8_relat_1(k3_relat_1(A_9),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_231])).

tff(c_113,plain,(
    ! [A_28] :
      ( k2_xboole_0(k1_relat_1(A_28),k2_relat_1(A_28)) = k3_relat_1(A_28)
      | ~ v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_119,plain,(
    ! [A_28] :
      ( k4_xboole_0(k1_relat_1(A_28),k3_relat_1(A_28)) = k1_xboole_0
      | ~ v1_relat_1(A_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_225,plain,(
    ! [B_39,A_40] :
      ( k7_relat_1(B_39,A_40) = B_39
      | ~ r1_tarski(k1_relat_1(B_39),A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_302,plain,(
    ! [B_48,B_49] :
      ( k7_relat_1(B_48,B_49) = B_48
      | ~ v1_relat_1(B_48)
      | k4_xboole_0(k1_relat_1(B_48),B_49) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_225])).

tff(c_317,plain,(
    ! [A_50] :
      ( k7_relat_1(A_50,k3_relat_1(A_50)) = A_50
      | ~ v1_relat_1(A_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_302])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k8_relat_1(A_14,k7_relat_1(B_15,A_14)) = k2_wellord1(B_15,A_14)
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_382,plain,(
    ! [A_55] :
      ( k8_relat_1(k3_relat_1(A_55),A_55) = k2_wellord1(A_55,k3_relat_1(A_55))
      | ~ v1_relat_1(A_55)
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_20])).

tff(c_397,plain,(
    ! [A_56] :
      ( k2_wellord1(A_56,k3_relat_1(A_56)) = A_56
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(A_56)
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_243,c_382])).

tff(c_22,plain,(
    k2_wellord1('#skF_1',k3_relat_1('#skF_1')) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_403,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_22])).

tff(c_411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_403])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n020.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:44:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  
% 1.96/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.22  %$ r1_tarski > v1_relat_1 > k8_relat_1 > k7_relat_1 > k4_xboole_0 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1
% 1.96/1.22  
% 1.96/1.22  %Foreground sorts:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Background operators:
% 1.96/1.22  
% 1.96/1.22  
% 1.96/1.22  %Foreground operators:
% 1.96/1.22  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.22  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.22  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.96/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.96/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.22  
% 2.09/1.23  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k2_wellord1(A, k3_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_wellord1)).
% 2.09/1.23  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 2.09/1.23  tff(f_34, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.23  tff(f_36, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 2.09/1.23  tff(f_32, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.09/1.23  tff(f_30, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.09/1.23  tff(f_46, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.09/1.23  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 2.09/1.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k8_relat_1(A, k7_relat_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_wellord1)).
% 2.09/1.23  tff(c_24, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.23  tff(c_14, plain, (![A_9]: (k2_xboole_0(k1_relat_1(A_9), k2_relat_1(A_9))=k3_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_10, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.23  tff(c_70, plain, (![A_22, B_23]: (k3_tarski(k2_tarski(A_22, B_23))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.09/1.23  tff(c_90, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(B_27, A_26))), inference(superposition, [status(thm), theory('equality')], [c_10, c_70])).
% 2.09/1.23  tff(c_12, plain, (![A_7, B_8]: (k3_tarski(k2_tarski(A_7, B_8))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.09/1.23  tff(c_125, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_90, c_12])).
% 2.09/1.23  tff(c_8, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.09/1.23  tff(c_164, plain, (![B_31, A_32]: (k4_xboole_0(B_31, k2_xboole_0(A_32, B_31))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_125, c_8])).
% 2.09/1.23  tff(c_180, plain, (![A_9]: (k4_xboole_0(k2_relat_1(A_9), k3_relat_1(A_9))=k1_xboole_0 | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_14, c_164])).
% 2.09/1.23  tff(c_4, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.09/1.23  tff(c_192, plain, (![A_33, B_34]: (k8_relat_1(A_33, B_34)=B_34 | ~r1_tarski(k2_relat_1(B_34), A_33) | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.09/1.23  tff(c_231, plain, (![B_41, B_42]: (k8_relat_1(B_41, B_42)=B_42 | ~v1_relat_1(B_42) | k4_xboole_0(k2_relat_1(B_42), B_41)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_192])).
% 2.09/1.23  tff(c_243, plain, (![A_9]: (k8_relat_1(k3_relat_1(A_9), A_9)=A_9 | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_180, c_231])).
% 2.09/1.23  tff(c_113, plain, (![A_28]: (k2_xboole_0(k1_relat_1(A_28), k2_relat_1(A_28))=k3_relat_1(A_28) | ~v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.09/1.23  tff(c_119, plain, (![A_28]: (k4_xboole_0(k1_relat_1(A_28), k3_relat_1(A_28))=k1_xboole_0 | ~v1_relat_1(A_28))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 2.09/1.23  tff(c_225, plain, (![B_39, A_40]: (k7_relat_1(B_39, A_40)=B_39 | ~r1_tarski(k1_relat_1(B_39), A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.23  tff(c_302, plain, (![B_48, B_49]: (k7_relat_1(B_48, B_49)=B_48 | ~v1_relat_1(B_48) | k4_xboole_0(k1_relat_1(B_48), B_49)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_225])).
% 2.09/1.23  tff(c_317, plain, (![A_50]: (k7_relat_1(A_50, k3_relat_1(A_50))=A_50 | ~v1_relat_1(A_50))), inference(superposition, [status(thm), theory('equality')], [c_119, c_302])).
% 2.09/1.23  tff(c_20, plain, (![A_14, B_15]: (k8_relat_1(A_14, k7_relat_1(B_15, A_14))=k2_wellord1(B_15, A_14) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.23  tff(c_382, plain, (![A_55]: (k8_relat_1(k3_relat_1(A_55), A_55)=k2_wellord1(A_55, k3_relat_1(A_55)) | ~v1_relat_1(A_55) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_317, c_20])).
% 2.09/1.23  tff(c_397, plain, (![A_56]: (k2_wellord1(A_56, k3_relat_1(A_56))=A_56 | ~v1_relat_1(A_56) | ~v1_relat_1(A_56) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_243, c_382])).
% 2.09/1.23  tff(c_22, plain, (k2_wellord1('#skF_1', k3_relat_1('#skF_1'))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.09/1.23  tff(c_403, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_397, c_22])).
% 2.09/1.23  tff(c_411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_403])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 0
% 2.09/1.23  #Sup     : 93
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 0
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 11
% 2.09/1.23  #Demod        : 7
% 2.09/1.23  #Tautology    : 62
% 2.09/1.23  #SimpNegUnit  : 0
% 2.09/1.23  #BackRed      : 0
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.10/1.24  Preprocessing        : 0.28
% 2.10/1.24  Parsing              : 0.15
% 2.10/1.24  CNF conversion       : 0.02
% 2.10/1.24  Main loop            : 0.20
% 2.10/1.24  Inferencing          : 0.09
% 2.10/1.24  Reduction            : 0.06
% 2.10/1.24  Demodulation         : 0.05
% 2.10/1.24  BG Simplification    : 0.01
% 2.10/1.24  Subsumption          : 0.02
% 2.10/1.24  Abstraction          : 0.01
% 2.10/1.24  MUC search           : 0.00
% 2.10/1.24  Cooper               : 0.00
% 2.10/1.24  Total                : 0.51
% 2.10/1.24  Index Insertion      : 0.00
% 2.10/1.24  Index Deletion       : 0.00
% 2.10/1.24  Index Matching       : 0.00
% 2.10/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
