%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:03 EST 2020

% Result     : Theorem 9.53s
% Output     : CNFRefutation 9.86s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 155 expanded)
%              Number of leaves         :   30 (  65 expanded)
%              Depth                    :   12
%              Number of atoms          :  102 ( 240 expanded)
%              Number of equality atoms :   30 ( 102 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(f_93,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k7_relat_1(B,A) = k7_relat_1(B,k3_xboole_0(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t192_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_37,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_70,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_88,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k7_relat_1(B_29,A_28),B_29)
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_12,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_27] : k1_relat_1(k6_relat_1(A_27)) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_239,plain,(
    ! [B_64,A_65] :
      ( k7_relat_1(B_64,A_65) = B_64
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_242,plain,(
    ! [A_27,A_65] :
      ( k7_relat_1(k6_relat_1(A_27),A_65) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_65)
      | ~ v1_relat_1(k6_relat_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_239])).

tff(c_244,plain,(
    ! [A_27,A_65] :
      ( k7_relat_1(k6_relat_1(A_27),A_65) = k6_relat_1(A_27)
      | ~ r1_tarski(A_27,A_65) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_242])).

tff(c_263,plain,(
    ! [B_70,A_71] :
      ( k3_xboole_0(k1_relat_1(B_70),A_71) = k1_relat_1(k7_relat_1(B_70,A_71))
      | ~ v1_relat_1(B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_104,plain,(
    ! [A_47,B_48] : k1_setfam_1(k2_tarski(A_47,B_48)) = k3_xboole_0(A_47,B_48) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [B_49,A_50] : k1_setfam_1(k2_tarski(B_49,A_50)) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_104])).

tff(c_10,plain,(
    ! [A_12,B_13] : k1_setfam_1(k2_tarski(A_12,B_13)) = k3_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_143,plain,(
    ! [B_51,A_52] : k3_xboole_0(B_51,A_52) = k3_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( v1_relat_1(k3_xboole_0(A_15,B_16))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_158,plain,(
    ! [B_51,A_52] :
      ( v1_relat_1(k3_xboole_0(B_51,A_52))
      | ~ v1_relat_1(A_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_14])).

tff(c_322,plain,(
    ! [B_76,A_77] :
      ( v1_relat_1(k1_relat_1(k7_relat_1(B_76,A_77)))
      | ~ v1_relat_1(A_77)
      | ~ v1_relat_1(B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_158])).

tff(c_328,plain,(
    ! [A_27,A_65] :
      ( v1_relat_1(k1_relat_1(k6_relat_1(A_27)))
      | ~ v1_relat_1(A_65)
      | ~ v1_relat_1(k6_relat_1(A_27))
      | ~ r1_tarski(A_27,A_65) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_322])).

tff(c_339,plain,(
    ! [A_80,A_81] :
      ( v1_relat_1(A_80)
      | ~ v1_relat_1(A_81)
      | ~ r1_tarski(A_80,A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26,c_328])).

tff(c_343,plain,(
    ! [B_29,A_28] :
      ( v1_relat_1(k7_relat_1(B_29,A_28))
      | ~ v1_relat_1(B_29) ) ),
    inference(resolution,[status(thm)],[c_30,c_339])).

tff(c_703,plain,(
    ! [A_117,B_118] :
      ( r1_tarski(k1_relat_1(A_117),k1_relat_1(B_118))
      | ~ r1_tarski(A_117,B_118)
      | ~ v1_relat_1(B_118)
      | ~ v1_relat_1(A_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_36,plain,(
    ! [B_35,A_34] :
      ( k7_relat_1(B_35,A_34) = B_35
      | ~ r1_tarski(k1_relat_1(B_35),A_34)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_828,plain,(
    ! [A_127,B_128] :
      ( k7_relat_1(A_127,k1_relat_1(B_128)) = A_127
      | ~ r1_tarski(A_127,B_128)
      | ~ v1_relat_1(B_128)
      | ~ v1_relat_1(A_127) ) ),
    inference(resolution,[status(thm)],[c_703,c_36])).

tff(c_125,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_10])).

tff(c_476,plain,(
    ! [A_101,B_102] :
      ( k3_xboole_0(A_101,k1_relat_1(B_102)) = k1_relat_1(k7_relat_1(B_102,A_101))
      | ~ v1_relat_1(B_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_263])).

tff(c_38,plain,(
    k7_relat_1('#skF_2',k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1')) != k7_relat_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    k7_relat_1('#skF_2',k3_xboole_0('#skF_1',k1_relat_1('#skF_2'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_38])).

tff(c_486,plain,
    ( k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_142])).

tff(c_522,plain,(
    k7_relat_1('#skF_2',k1_relat_1(k7_relat_1('#skF_2','#skF_1'))) != k7_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_486])).

tff(c_837,plain,
    ( k7_relat_1('#skF_2','#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_522])).

tff(c_892,plain,
    ( k7_relat_1('#skF_2','#skF_1') != '#skF_2'
    | ~ r1_tarski('#skF_2',k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_837])).

tff(c_908,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_892])).

tff(c_911,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_343,c_908])).

tff(c_915,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_911])).

tff(c_917,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_892])).

tff(c_16,plain,(
    ! [C_19,A_17,B_18] :
      ( k7_relat_1(k7_relat_1(C_19,A_17),B_18) = k7_relat_1(C_19,k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13796,plain,(
    ! [C_457,A_458,B_459] :
      ( k7_relat_1(C_457,k3_xboole_0(A_458,k1_relat_1(B_459))) = k7_relat_1(C_457,A_458)
      | ~ v1_relat_1(C_457)
      | ~ r1_tarski(k7_relat_1(C_457,A_458),B_459)
      | ~ v1_relat_1(B_459)
      | ~ v1_relat_1(k7_relat_1(C_457,A_458)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_828,c_16])).

tff(c_14057,plain,
    ( ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2')
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_13796,c_142])).

tff(c_14215,plain,(
    ~ r1_tarski(k7_relat_1('#skF_2','#skF_1'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_917,c_40,c_14057])).

tff(c_14237,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_14215])).

tff(c_14241,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_14237])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.53/3.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.38  
% 9.53/3.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.53/3.38  %$ r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 9.53/3.38  
% 9.53/3.38  %Foreground sorts:
% 9.53/3.38  
% 9.53/3.38  
% 9.53/3.38  %Background operators:
% 9.53/3.38  
% 9.53/3.38  
% 9.53/3.38  %Foreground operators:
% 9.53/3.38  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 9.53/3.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.53/3.38  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.53/3.38  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 9.53/3.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.53/3.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.53/3.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.53/3.38  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.53/3.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.53/3.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.53/3.38  tff('#skF_2', type, '#skF_2': $i).
% 9.53/3.38  tff('#skF_1', type, '#skF_1': $i).
% 9.53/3.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.53/3.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.53/3.38  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 9.53/3.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.53/3.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.53/3.38  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.53/3.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 9.53/3.38  
% 9.86/3.39  tff(f_93, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k7_relat_1(B, k3_xboole_0(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t192_relat_1)).
% 9.86/3.39  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 9.86/3.39  tff(f_37, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 9.86/3.39  tff(f_70, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 9.86/3.39  tff(f_88, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 9.86/3.39  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 9.86/3.39  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 9.86/3.39  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 9.86/3.39  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_relat_1)).
% 9.86/3.39  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_relat_1)).
% 9.86/3.39  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 9.86/3.39  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.86/3.39  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k7_relat_1(B_29, A_28), B_29) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 9.86/3.39  tff(c_12, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 9.86/3.39  tff(c_26, plain, (![A_27]: (k1_relat_1(k6_relat_1(A_27))=A_27)), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.86/3.39  tff(c_239, plain, (![B_64, A_65]: (k7_relat_1(B_64, A_65)=B_64 | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.86/3.39  tff(c_242, plain, (![A_27, A_65]: (k7_relat_1(k6_relat_1(A_27), A_65)=k6_relat_1(A_27) | ~r1_tarski(A_27, A_65) | ~v1_relat_1(k6_relat_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_239])).
% 9.86/3.39  tff(c_244, plain, (![A_27, A_65]: (k7_relat_1(k6_relat_1(A_27), A_65)=k6_relat_1(A_27) | ~r1_tarski(A_27, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_242])).
% 9.86/3.39  tff(c_263, plain, (![B_70, A_71]: (k3_xboole_0(k1_relat_1(B_70), A_71)=k1_relat_1(k7_relat_1(B_70, A_71)) | ~v1_relat_1(B_70))), inference(cnfTransformation, [status(thm)], [f_78])).
% 9.86/3.39  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.86/3.39  tff(c_104, plain, (![A_47, B_48]: (k1_setfam_1(k2_tarski(A_47, B_48))=k3_xboole_0(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.39  tff(c_119, plain, (![B_49, A_50]: (k1_setfam_1(k2_tarski(B_49, A_50))=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_2, c_104])).
% 9.86/3.39  tff(c_10, plain, (![A_12, B_13]: (k1_setfam_1(k2_tarski(A_12, B_13))=k3_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.86/3.39  tff(c_143, plain, (![B_51, A_52]: (k3_xboole_0(B_51, A_52)=k3_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_119, c_10])).
% 9.86/3.39  tff(c_14, plain, (![A_15, B_16]: (v1_relat_1(k3_xboole_0(A_15, B_16)) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.86/3.39  tff(c_158, plain, (![B_51, A_52]: (v1_relat_1(k3_xboole_0(B_51, A_52)) | ~v1_relat_1(A_52))), inference(superposition, [status(thm), theory('equality')], [c_143, c_14])).
% 9.86/3.39  tff(c_322, plain, (![B_76, A_77]: (v1_relat_1(k1_relat_1(k7_relat_1(B_76, A_77))) | ~v1_relat_1(A_77) | ~v1_relat_1(B_76))), inference(superposition, [status(thm), theory('equality')], [c_263, c_158])).
% 9.86/3.39  tff(c_328, plain, (![A_27, A_65]: (v1_relat_1(k1_relat_1(k6_relat_1(A_27))) | ~v1_relat_1(A_65) | ~v1_relat_1(k6_relat_1(A_27)) | ~r1_tarski(A_27, A_65))), inference(superposition, [status(thm), theory('equality')], [c_244, c_322])).
% 9.86/3.39  tff(c_339, plain, (![A_80, A_81]: (v1_relat_1(A_80) | ~v1_relat_1(A_81) | ~r1_tarski(A_80, A_81))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26, c_328])).
% 9.86/3.39  tff(c_343, plain, (![B_29, A_28]: (v1_relat_1(k7_relat_1(B_29, A_28)) | ~v1_relat_1(B_29))), inference(resolution, [status(thm)], [c_30, c_339])).
% 9.86/3.39  tff(c_703, plain, (![A_117, B_118]: (r1_tarski(k1_relat_1(A_117), k1_relat_1(B_118)) | ~r1_tarski(A_117, B_118) | ~v1_relat_1(B_118) | ~v1_relat_1(A_117))), inference(cnfTransformation, [status(thm)], [f_66])).
% 9.86/3.39  tff(c_36, plain, (![B_35, A_34]: (k7_relat_1(B_35, A_34)=B_35 | ~r1_tarski(k1_relat_1(B_35), A_34) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_88])).
% 9.86/3.39  tff(c_828, plain, (![A_127, B_128]: (k7_relat_1(A_127, k1_relat_1(B_128))=A_127 | ~r1_tarski(A_127, B_128) | ~v1_relat_1(B_128) | ~v1_relat_1(A_127))), inference(resolution, [status(thm)], [c_703, c_36])).
% 9.86/3.39  tff(c_125, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(superposition, [status(thm), theory('equality')], [c_119, c_10])).
% 9.86/3.39  tff(c_476, plain, (![A_101, B_102]: (k3_xboole_0(A_101, k1_relat_1(B_102))=k1_relat_1(k7_relat_1(B_102, A_101)) | ~v1_relat_1(B_102))), inference(superposition, [status(thm), theory('equality')], [c_125, c_263])).
% 9.86/3.39  tff(c_38, plain, (k7_relat_1('#skF_2', k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1'))!=k7_relat_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 9.86/3.39  tff(c_142, plain, (k7_relat_1('#skF_2', k3_xboole_0('#skF_1', k1_relat_1('#skF_2')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_38])).
% 9.86/3.39  tff(c_486, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_476, c_142])).
% 9.86/3.39  tff(c_522, plain, (k7_relat_1('#skF_2', k1_relat_1(k7_relat_1('#skF_2', '#skF_1')))!=k7_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_486])).
% 9.86/3.39  tff(c_837, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_828, c_522])).
% 9.86/3.39  tff(c_892, plain, (k7_relat_1('#skF_2', '#skF_1')!='#skF_2' | ~r1_tarski('#skF_2', k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_837])).
% 9.86/3.39  tff(c_908, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_892])).
% 9.86/3.39  tff(c_911, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_343, c_908])).
% 9.86/3.39  tff(c_915, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_911])).
% 9.86/3.39  tff(c_917, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_892])).
% 9.86/3.39  tff(c_16, plain, (![C_19, A_17, B_18]: (k7_relat_1(k7_relat_1(C_19, A_17), B_18)=k7_relat_1(C_19, k3_xboole_0(A_17, B_18)) | ~v1_relat_1(C_19))), inference(cnfTransformation, [status(thm)], [f_45])).
% 9.86/3.39  tff(c_13796, plain, (![C_457, A_458, B_459]: (k7_relat_1(C_457, k3_xboole_0(A_458, k1_relat_1(B_459)))=k7_relat_1(C_457, A_458) | ~v1_relat_1(C_457) | ~r1_tarski(k7_relat_1(C_457, A_458), B_459) | ~v1_relat_1(B_459) | ~v1_relat_1(k7_relat_1(C_457, A_458)))), inference(superposition, [status(thm), theory('equality')], [c_828, c_16])).
% 9.86/3.39  tff(c_14057, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2') | ~v1_relat_1('#skF_2') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_13796, c_142])).
% 9.86/3.39  tff(c_14215, plain, (~r1_tarski(k7_relat_1('#skF_2', '#skF_1'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_917, c_40, c_14057])).
% 9.86/3.39  tff(c_14237, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_14215])).
% 9.86/3.39  tff(c_14241, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_14237])).
% 9.86/3.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.86/3.39  
% 9.86/3.39  Inference rules
% 9.86/3.39  ----------------------
% 9.86/3.39  #Ref     : 0
% 9.86/3.39  #Sup     : 3725
% 9.86/3.39  #Fact    : 0
% 9.86/3.39  #Define  : 0
% 9.86/3.39  #Split   : 2
% 9.86/3.39  #Chain   : 0
% 9.86/3.39  #Close   : 0
% 9.86/3.39  
% 9.86/3.39  Ordering : KBO
% 9.86/3.39  
% 9.86/3.39  Simplification rules
% 9.86/3.39  ----------------------
% 9.86/3.39  #Subsume      : 842
% 9.86/3.39  #Demod        : 1965
% 9.86/3.39  #Tautology    : 835
% 9.86/3.39  #SimpNegUnit  : 0
% 9.86/3.39  #BackRed      : 1
% 9.86/3.39  
% 9.86/3.39  #Partial instantiations: 0
% 9.86/3.39  #Strategies tried      : 1
% 9.86/3.39  
% 9.86/3.39  Timing (in seconds)
% 9.86/3.39  ----------------------
% 9.86/3.40  Preprocessing        : 0.32
% 9.86/3.40  Parsing              : 0.17
% 9.86/3.40  CNF conversion       : 0.02
% 9.86/3.40  Main loop            : 2.31
% 9.86/3.40  Inferencing          : 0.60
% 9.86/3.40  Reduction            : 0.83
% 9.86/3.40  Demodulation         : 0.66
% 9.86/3.40  BG Simplification    : 0.08
% 9.86/3.40  Subsumption          : 0.65
% 9.86/3.40  Abstraction          : 0.11
% 9.86/3.40  MUC search           : 0.00
% 9.86/3.40  Cooper               : 0.00
% 9.86/3.40  Total                : 2.67
% 9.86/3.40  Index Insertion      : 0.00
% 9.86/3.40  Index Deletion       : 0.00
% 9.86/3.40  Index Matching       : 0.00
% 9.86/3.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
