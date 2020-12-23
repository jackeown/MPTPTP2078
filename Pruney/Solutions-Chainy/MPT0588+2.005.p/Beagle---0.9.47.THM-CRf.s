%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 9.57s
% Output     : CNFRefutation 9.57s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 152 expanded)
%              Number of leaves         :   27 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 240 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_35,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_33,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_24,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k7_relat_1(B_21,A_20),B_21)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_10] : v1_relat_1(k6_relat_1(A_10)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_19] : k1_relat_1(k6_relat_1(A_19)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_193,plain,(
    ! [B_50,A_51] :
      ( k7_relat_1(B_50,A_51) = B_50
      | ~ r1_tarski(k1_relat_1(B_50),A_51)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_196,plain,(
    ! [A_19,A_51] :
      ( k7_relat_1(k6_relat_1(A_19),A_51) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_51)
      | ~ v1_relat_1(k6_relat_1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_193])).

tff(c_198,plain,(
    ! [A_19,A_51] :
      ( k7_relat_1(k6_relat_1(A_19),A_51) = k6_relat_1(A_19)
      | ~ r1_tarski(A_19,A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_196])).

tff(c_199,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(k1_relat_1(B_52),A_53) = k1_relat_1(k7_relat_1(B_52,A_53))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_98,plain,(
    ! [A_39,B_40] : k1_setfam_1(k2_tarski(A_39,B_40)) = k3_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_113,plain,(
    ! [B_41,A_42] : k1_setfam_1(k2_tarski(B_41,A_42)) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_8,plain,(
    ! [A_8,B_9] : k1_setfam_1(k2_tarski(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_137,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_12,plain,(
    ! [A_11,B_12] :
      ( v1_relat_1(k3_xboole_0(A_11,B_12))
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [B_43,A_44] :
      ( v1_relat_1(k3_xboole_0(B_43,A_44))
      | ~ v1_relat_1(A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_12])).

tff(c_276,plain,(
    ! [B_62,A_63] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(B_62,A_63)))
      | ~ v1_relat_1(A_63)
      | ~ v1_relat_1(B_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_152])).

tff(c_279,plain,(
    ! [A_19,A_51] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(A_19)))
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(k6_relat_1(A_19))
      | ~ r1_tarski(A_19,A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_276])).

tff(c_306,plain,(
    ! [A_68,A_69] :
      ( v1_relat_1(A_68)
      | ~ v1_relat_1(A_69)
      | ~ r1_tarski(A_68,A_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20,c_279])).

tff(c_310,plain,(
    ! [B_21,A_20] :
      ( v1_relat_1(k7_relat_1(B_21,A_20))
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_24,c_306])).

tff(c_317,plain,(
    ! [A_72,B_73] :
      ( r1_tarski(k1_relat_1(A_72),k1_relat_1(B_73))
      | ~ r1_tarski(A_72,B_73)
      | ~ v1_relat_1(B_73)
      | ~ v1_relat_1(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( k7_relat_1(B_27,A_26) = B_27
      | ~ r1_tarski(k1_relat_1(B_27),A_26)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_587,plain,(
    ! [A_97,B_98] :
      ( k7_relat_1(A_97,k1_relat_1(B_98)) = A_97
      | ~ r1_tarski(A_97,B_98)
      | ~ v1_relat_1(B_98)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_317,c_30])).

tff(c_119,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_8])).

tff(c_479,plain,(
    ! [A_89,B_90] :
      ( k3_xboole_0(A_89,k1_relat_1(B_90)) = k1_relat_1(k7_relat_1(B_90,A_89))
      | ~ v1_relat_1(B_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_199,c_119])).

tff(c_32,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_136,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_32])).

tff(c_489,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_479,c_136])).

tff(c_525,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_489])).

tff(c_593,plain,
    ( k7_relat_1('#skF_2','#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_525])).

tff(c_643,plain,
    ( k7_relat_1('#skF_2','#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_593])).

tff(c_724,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_643])).

tff(c_727,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_310,c_724])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_727])).

tff(c_733,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_643])).

tff(c_14,plain,(
    ! [C_15,A_13,B_14] :
      ( k7_relat_1(k7_relat_1(C_15,A_13),B_14) = k7_relat_1(C_15,k3_xboole_0(A_13,B_14))
      | ~ v1_relat_1(C_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_13400,plain,(
    ! [C_459,A_460,B_461] :
      ( k7_relat_1(C_459,k3_xboole_0(A_460,k1_relat_1(B_461))) = k7_relat_1(C_459,A_460)
      | ~ v1_relat_1(C_459)
      | ~ r1_tarski(k7_relat_1(C_459,A_460),B_461)
      | ~ v1_relat_1(B_461)
      | ~ v1_relat_1(k7_relat_1(C_459,A_460)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_14])).

tff(c_13680,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13400,c_136])).

tff(c_13838,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_733,c_34,c_13680])).

tff(c_13852,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_13838])).

tff(c_13856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_13852])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:51:16 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.57/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.47  
% 9.57/3.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.47  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.57/3.47  
% 9.57/3.47  %Foreground sorts:
% 9.57/3.47  
% 9.57/3.47  
% 9.57/3.47  %Background operators:
% 9.57/3.47  
% 9.57/3.47  
% 9.57/3.47  %Foreground operators:
% 9.57/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.57/3.47  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.57/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.57/3.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.57/3.47  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.57/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.57/3.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.57/3.47  tff('#skF_2', type, '#skF_2': $i).
% 9.57/3.47  tff('#skF_1', type, '#skF_1': $i).
% 9.57/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.57/3.47  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.57/3.47  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.57/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.57/3.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.57/3.47  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.57/3.47  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.57/3.47  
% 9.57/3.48  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 9.57/3.48  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 9.57/3.48  tff(f_35, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.57/3.48  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.57/3.48  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.57/3.48  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 9.57/3.48  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.57/3.48  tff(f_33, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.57/3.48  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 9.57/3.48  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.57/3.48  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 9.57/3.48  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.57/3.48  tff(c_24, plain, (![B_21, A_20]: (r1_tarski(k7_relat_1(B_21, A_20), B_21) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_62])).
% 9.57/3.48  tff(c_10, plain, (![A_10]: (v1_relat_1(k6_relat_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.57/3.48  tff(c_20, plain, (![A_19]: (k1_relat_1(k6_relat_1(A_19))=A_19)), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.57/3.48  tff(c_193, plain, (![B_50, A_51]: (k7_relat_1(B_50, A_51)=B_50 | ~r1_tarski(k1_relat_1(B_50), A_51) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.48  tff(c_196, plain, (![A_19, A_51]: (k7_relat_1(k6_relat_1(A_19), A_51)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_51) | ~v1_relat_1(k6_relat_1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_193])).
% 9.57/3.48  tff(c_198, plain, (![A_19, A_51]: (k7_relat_1(k6_relat_1(A_19), A_51)=k6_relat_1(A_19) | ~r1_tarski(A_19, A_51))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_196])).
% 9.57/3.48  tff(c_199, plain, (![B_52, A_53]: (k3_xboole_0(k1_relat_1(B_52), A_53)=k1_relat_1(k7_relat_1(B_52, A_53)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.57/3.48  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.57/3.48  tff(c_98, plain, (![A_39, B_40]: (k1_setfam_1(k2_tarski(A_39, B_40))=k3_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.57/3.48  tff(c_113, plain, (![B_41, A_42]: (k1_setfam_1(k2_tarski(B_41, A_42))=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_2, c_98])).
% 9.57/3.48  tff(c_8, plain, (![A_8, B_9]: (k1_setfam_1(k2_tarski(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 9.57/3.48  tff(c_137, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 9.57/3.48  tff(c_12, plain, (![A_11, B_12]: (v1_relat_1(k3_xboole_0(A_11, B_12)) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 9.57/3.48  tff(c_152, plain, (![B_43, A_44]: (v1_relat_1(k3_xboole_0(B_43, A_44)) | ~v1_relat_1(A_44))), inference(superposition, [status(thm), theory('equality')], [c_137, c_12])).
% 9.57/3.48  tff(c_276, plain, (![B_62, A_63]: (v1_relat_1(k1_relat_1(k7_relat_1(B_62, A_63))) | ~v1_relat_1(A_63) | ~v1_relat_1(B_62))), inference(superposition, [status(thm), theory('equality')], [c_199, c_152])).
% 9.57/3.48  tff(c_279, plain, (![A_19, A_51]: (v1_relat_1(k1_relat_1(k6_relat_1(A_19))) | ~v1_relat_1(A_51) | ~v1_relat_1(k6_relat_1(A_19)) | ~r1_tarski(A_19, A_51))), inference(superposition, [status(thm), theory('equality')], [c_198, c_276])).
% 9.57/3.48  tff(c_306, plain, (![A_68, A_69]: (v1_relat_1(A_68) | ~v1_relat_1(A_69) | ~r1_tarski(A_68, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_20, c_279])).
% 9.57/3.48  tff(c_310, plain, (![B_21, A_20]: (v1_relat_1(k7_relat_1(B_21, A_20)) | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_24, c_306])).
% 9.57/3.48  tff(c_317, plain, (![A_72, B_73]: (r1_tarski(k1_relat_1(A_72), k1_relat_1(B_73)) | ~r1_tarski(A_72, B_73) | ~v1_relat_1(B_73) | ~v1_relat_1(A_72))), inference(cnfTransformation, [status(thm)], [f_54])).
% 9.57/3.48  tff(c_30, plain, (![B_27, A_26]: (k7_relat_1(B_27, A_26)=B_27 | ~r1_tarski(k1_relat_1(B_27), A_26) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.57/3.48  tff(c_587, plain, (![A_97, B_98]: (k7_relat_1(A_97, k1_relat_1(B_98))=A_97 | ~r1_tarski(A_97, B_98) | ~v1_relat_1(B_98) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_317, c_30])).
% 9.57/3.48  tff(c_119, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_113, c_8])).
% 9.57/3.48  tff(c_479, plain, (![A_89, B_90]: (k3_xboole_0(A_89, k1_relat_1(B_90))=k1_relat_1(k7_relat_1(B_90, A_89)) | ~v1_relat_1(B_90))), inference(superposition, [status(thm), theory('equality')], [c_199, c_119])).
% 9.57/3.48  tff(c_32, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.57/3.48  tff(c_136, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_119, c_32])).
% 9.57/3.48  tff(c_489, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_479, c_136])).
% 9.57/3.48  tff(c_525, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_489])).
% 9.57/3.48  tff(c_593, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_587, c_525])).
% 9.57/3.48  tff(c_643, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_593])).
% 9.57/3.48  tff(c_724, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_643])).
% 9.57/3.48  tff(c_727, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_310, c_724])).
% 9.57/3.48  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_727])).
% 9.57/3.48  tff(c_733, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_643])).
% 9.57/3.48  tff(c_14, plain, (![C_15, A_13, B_14]: (k7_relat_1(k7_relat_1(C_15, A_13), B_14)=k7_relat_1(C_15, k3_xboole_0(A_13, B_14)) | ~v1_relat_1(C_15))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.57/3.48  tff(c_13400, plain, (![C_459, A_460, B_461]: (k7_relat_1(C_459, k3_xboole_0(A_460, k1_relat_1(B_461)))=k7_relat_1(C_459, A_460) | ~v1_relat_1(C_459) | ~r1_tarski(k7_relat_1(C_459, A_460), B_461) | ~v1_relat_1(B_461) | ~v1_relat_1(k7_relat_1(C_459, A_460)))), inference(superposition, [status(thm), theory('equality')], [c_587, c_14])).
% 9.57/3.48  tff(c_13680, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13400, c_136])).
% 9.57/3.48  tff(c_13838, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_733, c_34, c_13680])).
% 9.57/3.48  tff(c_13852, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_13838])).
% 9.57/3.48  tff(c_13856, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_13852])).
% 9.57/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.57/3.48  
% 9.57/3.48  Inference rules
% 9.57/3.48  ----------------------
% 9.57/3.48  #Ref     : 0
% 9.57/3.48  #Sup     : 3719
% 9.57/3.48  #Fact    : 0
% 9.57/3.48  #Define  : 0
% 9.57/3.48  #Split   : 2
% 9.57/3.48  #Chain   : 0
% 9.57/3.48  #Close   : 0
% 9.57/3.48  
% 9.57/3.48  Ordering : KBO
% 9.57/3.48  
% 9.57/3.48  Simplification rules
% 9.57/3.48  ----------------------
% 9.57/3.48  #Subsume      : 891
% 9.57/3.48  #Demod        : 1793
% 9.57/3.48  #Tautology    : 756
% 9.57/3.48  #SimpNegUnit  : 0
% 9.57/3.48  #BackRed      : 1
% 9.57/3.48  
% 9.57/3.48  #Partial instantiations: 0
% 9.57/3.48  #Strategies tried      : 1
% 9.57/3.48  
% 9.57/3.48  Timing (in seconds)
% 9.57/3.48  ----------------------
% 9.57/3.48  Preprocessing        : 0.29
% 9.57/3.48  Parsing              : 0.16
% 9.57/3.48  CNF conversion       : 0.02
% 9.57/3.48  Main loop            : 2.40
% 9.57/3.48  Inferencing          : 0.58
% 9.57/3.48  Reduction            : 0.87
% 9.57/3.48  Demodulation         : 0.70
% 9.57/3.48  BG Simplification    : 0.08
% 9.57/3.48  Subsumption          : 0.71
% 9.57/3.48  Abstraction          : 0.11
% 9.57/3.48  MUC search           : 0.00
% 9.57/3.48  Cooper               : 0.00
% 9.57/3.48  Total                : 2.73
% 9.57/3.48  Index Insertion      : 0.00
% 9.57/3.48  Index Deletion       : 0.00
% 9.57/3.48  Index Matching       : 0.00
% 9.57/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
