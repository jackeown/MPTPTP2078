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
% DateTime   : Thu Dec  3 10:04:47 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 160 expanded)
%              Number of leaves         :   35 (  70 expanded)
%              Depth                    :   14
%              Number of atoms          :   82 ( 269 expanded)
%              Number of equality atoms :   37 (  83 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_42,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_42])).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_82,plain,(
    ! [A_62,B_63] :
      ( k4_xboole_0(A_62,B_63) = k1_xboole_0
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_94,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_82])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_65,B_66] : k5_xboole_0(A_65,k3_xboole_0(A_65,B_66)) = k4_xboole_0(A_65,B_66) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_115,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_118,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_115])).

tff(c_30,plain,(
    ! [A_38,B_39] :
      ( v1_relat_1(k7_relat_1(A_38,B_39))
      | ~ v1_relat_1(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_44,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_197,plain,(
    ! [B_79,A_80] :
      ( k1_relat_1(k7_relat_1(B_79,A_80)) = A_80
      | ~ r1_tarski(A_80,k1_relat_1(B_79))
      | ~ v1_relat_1(B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_204,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_197])).

tff(c_212,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_204])).

tff(c_233,plain,(
    ! [B_85] :
      ( k1_relat_1(k7_relat_1(B_85,k1_relat_1(B_85))) = k1_relat_1(B_85)
      | ~ v1_relat_1(B_85) ) ),
    inference(resolution,[status(thm)],[c_8,c_197])).

tff(c_254,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_233])).

tff(c_257,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_254])).

tff(c_258,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_262,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_258])).

tff(c_266,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_262])).

tff(c_268,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_32,plain,(
    ! [A_40] :
      ( k9_relat_1(A_40,k1_relat_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_229,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_32])).

tff(c_413,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_229])).

tff(c_34,plain,(
    ! [A_41,C_45,B_44] :
      ( k9_relat_1(k7_relat_1(A_41,C_45),B_44) = k9_relat_1(A_41,B_44)
      | ~ r1_tarski(B_44,C_45)
      | ~ v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_417,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_413,c_34])).

tff(c_424,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8,c_417])).

tff(c_36,plain,(
    ! [A_46] :
      ( k10_relat_1(A_46,k2_relat_1(A_46)) = k1_relat_1(A_46)
      | ~ v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_432,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_36])).

tff(c_436,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_212,c_432])).

tff(c_283,plain,(
    ! [A_86,C_87,B_88] :
      ( k3_xboole_0(A_86,k10_relat_1(C_87,B_88)) = k10_relat_1(k7_relat_1(C_87,A_86),B_88)
      | ~ v1_relat_1(C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_553,plain,(
    ! [A_105,C_106,B_107] :
      ( k5_xboole_0(A_105,k10_relat_1(k7_relat_1(C_106,A_105),B_107)) = k4_xboole_0(A_105,k10_relat_1(C_106,B_107))
      | ~ v1_relat_1(C_106) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_14])).

tff(c_571,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_436,c_553])).

tff(c_587,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_118,c_571])).

tff(c_589,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_587])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:02:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.43  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.43  
% 2.49/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.44  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.49/1.44  
% 2.49/1.44  %Foreground sorts:
% 2.49/1.44  
% 2.49/1.44  
% 2.49/1.44  %Background operators:
% 2.49/1.44  
% 2.49/1.44  
% 2.49/1.44  %Foreground operators:
% 2.49/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.44  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.49/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.44  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.49/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.44  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.49/1.44  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.49/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.49/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.49/1.44  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.49/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.44  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.44  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.44  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.49/1.44  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.44  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.49/1.44  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.49/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.44  
% 2.86/1.45  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.86/1.45  tff(f_89, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 2.86/1.45  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.86/1.45  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.86/1.45  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.86/1.45  tff(f_57, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.86/1.45  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 2.86/1.45  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 2.86/1.45  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.86/1.45  tff(f_72, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.86/1.45  tff(f_82, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 2.86/1.45  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | k4_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.45  tff(c_42, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.45  tff(c_63, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_10, c_42])).
% 2.86/1.45  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.45  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.86/1.45  tff(c_82, plain, (![A_62, B_63]: (k4_xboole_0(A_62, B_63)=k1_xboole_0 | ~r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.86/1.45  tff(c_94, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_82])).
% 2.86/1.45  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.86/1.45  tff(c_106, plain, (![A_65, B_66]: (k5_xboole_0(A_65, k3_xboole_0(A_65, B_66))=k4_xboole_0(A_65, B_66))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.45  tff(c_115, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 2.86/1.45  tff(c_118, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_94, c_115])).
% 2.86/1.45  tff(c_30, plain, (![A_38, B_39]: (v1_relat_1(k7_relat_1(A_38, B_39)) | ~v1_relat_1(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.86/1.45  tff(c_44, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.86/1.45  tff(c_197, plain, (![B_79, A_80]: (k1_relat_1(k7_relat_1(B_79, A_80))=A_80 | ~r1_tarski(A_80, k1_relat_1(B_79)) | ~v1_relat_1(B_79))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.86/1.45  tff(c_204, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_44, c_197])).
% 2.86/1.45  tff(c_212, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_204])).
% 2.86/1.45  tff(c_233, plain, (![B_85]: (k1_relat_1(k7_relat_1(B_85, k1_relat_1(B_85)))=k1_relat_1(B_85) | ~v1_relat_1(B_85))), inference(resolution, [status(thm)], [c_8, c_197])).
% 2.86/1.45  tff(c_254, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_233])).
% 2.86/1.45  tff(c_257, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_254])).
% 2.86/1.45  tff(c_258, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_257])).
% 2.86/1.45  tff(c_262, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_258])).
% 2.86/1.45  tff(c_266, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_262])).
% 2.86/1.45  tff(c_268, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_257])).
% 2.86/1.45  tff(c_32, plain, (![A_40]: (k9_relat_1(A_40, k1_relat_1(A_40))=k2_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.86/1.45  tff(c_229, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_212, c_32])).
% 2.86/1.45  tff(c_413, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_229])).
% 2.86/1.45  tff(c_34, plain, (![A_41, C_45, B_44]: (k9_relat_1(k7_relat_1(A_41, C_45), B_44)=k9_relat_1(A_41, B_44) | ~r1_tarski(B_44, C_45) | ~v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.86/1.45  tff(c_417, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_413, c_34])).
% 2.86/1.45  tff(c_424, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8, c_417])).
% 2.86/1.45  tff(c_36, plain, (![A_46]: (k10_relat_1(A_46, k2_relat_1(A_46))=k1_relat_1(A_46) | ~v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.86/1.45  tff(c_432, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_424, c_36])).
% 2.86/1.45  tff(c_436, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_268, c_212, c_432])).
% 2.86/1.45  tff(c_283, plain, (![A_86, C_87, B_88]: (k3_xboole_0(A_86, k10_relat_1(C_87, B_88))=k10_relat_1(k7_relat_1(C_87, A_86), B_88) | ~v1_relat_1(C_87))), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.86/1.45  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.45  tff(c_553, plain, (![A_105, C_106, B_107]: (k5_xboole_0(A_105, k10_relat_1(k7_relat_1(C_106, A_105), B_107))=k4_xboole_0(A_105, k10_relat_1(C_106, B_107)) | ~v1_relat_1(C_106))), inference(superposition, [status(thm), theory('equality')], [c_283, c_14])).
% 2.86/1.45  tff(c_571, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_436, c_553])).
% 2.86/1.45  tff(c_587, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_46, c_118, c_571])).
% 2.86/1.45  tff(c_589, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_587])).
% 2.86/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.45  
% 2.86/1.45  Inference rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Ref     : 0
% 2.86/1.45  #Sup     : 131
% 2.86/1.45  #Fact    : 0
% 2.86/1.45  #Define  : 0
% 2.86/1.45  #Split   : 3
% 2.86/1.45  #Chain   : 0
% 2.86/1.45  #Close   : 0
% 2.86/1.45  
% 2.86/1.45  Ordering : KBO
% 2.86/1.45  
% 2.86/1.45  Simplification rules
% 2.86/1.45  ----------------------
% 2.86/1.45  #Subsume      : 4
% 2.86/1.45  #Demod        : 66
% 2.86/1.45  #Tautology    : 74
% 2.86/1.45  #SimpNegUnit  : 1
% 2.86/1.45  #BackRed      : 1
% 2.86/1.45  
% 2.86/1.45  #Partial instantiations: 0
% 2.86/1.45  #Strategies tried      : 1
% 2.86/1.45  
% 2.86/1.45  Timing (in seconds)
% 2.86/1.45  ----------------------
% 2.86/1.45  Preprocessing        : 0.35
% 2.86/1.45  Parsing              : 0.19
% 2.86/1.45  CNF conversion       : 0.02
% 2.86/1.45  Main loop            : 0.28
% 2.86/1.45  Inferencing          : 0.10
% 2.86/1.45  Reduction            : 0.09
% 2.86/1.45  Demodulation         : 0.07
% 2.86/1.45  BG Simplification    : 0.02
% 2.86/1.45  Subsumption          : 0.05
% 2.86/1.45  Abstraction          : 0.02
% 2.86/1.45  MUC search           : 0.00
% 2.86/1.45  Cooper               : 0.00
% 2.86/1.45  Total                : 0.66
% 2.86/1.45  Index Insertion      : 0.00
% 2.86/1.45  Index Deletion       : 0.00
% 2.86/1.45  Index Matching       : 0.00
% 2.86/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
