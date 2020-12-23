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
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 4.49s
% Output     : CNFRefutation 4.49s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 478 expanded)
%              Number of leaves         :   28 ( 173 expanded)
%              Depth                    :   21
%              Number of atoms          :  103 ( 800 expanded)
%              Number of equality atoms :   43 ( 382 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_72,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_58,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_68,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( v1_relat_1(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    ! [A_21] : v1_relat_1(k6_relat_1(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_20,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_166,plain,(
    ! [B_43,A_44] :
      ( k7_relat_1(B_43,A_44) = B_43
      | ~ r1_tarski(k1_relat_1(B_43),A_44)
      | ~ v1_relat_1(B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_176,plain,(
    ! [B_43] :
      ( k7_relat_1(B_43,k1_relat_1(B_43)) = B_43
      | ~ v1_relat_1(B_43) ) ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_265,plain,(
    ! [B_52,A_53] :
      ( k3_xboole_0(k1_relat_1(B_52),A_53) = k1_relat_1(k7_relat_1(B_52,A_53))
      | ~ v1_relat_1(B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_297,plain,(
    ! [A_16,A_53] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_16),A_53)) = k3_xboole_0(A_16,A_53)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_265])).

tff(c_302,plain,(
    ! [A_54,A_55] : k1_relat_1(k7_relat_1(k6_relat_1(A_54),A_55)) = k3_xboole_0(A_54,A_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_297])).

tff(c_330,plain,(
    ! [A_54] :
      ( k3_xboole_0(A_54,k1_relat_1(k6_relat_1(A_54))) = k1_relat_1(k6_relat_1(A_54))
      | ~ v1_relat_1(k6_relat_1(A_54)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_302])).

tff(c_336,plain,(
    ! [A_54] : k3_xboole_0(A_54,A_54) = A_54 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_20,c_20,c_330])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_169,plain,(
    ! [A_16,A_44] :
      ( k7_relat_1(k6_relat_1(A_16),A_44) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_44)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_166])).

tff(c_175,plain,(
    ! [A_16,A_44] :
      ( k7_relat_1(k6_relat_1(A_16),A_44) = k6_relat_1(A_16)
      | ~ r1_tarski(A_16,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_169])).

tff(c_323,plain,(
    ! [A_16,A_44] :
      ( k3_xboole_0(A_16,A_44) = k1_relat_1(k6_relat_1(A_16))
      | ~ r1_tarski(A_16,A_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_302])).

tff(c_424,plain,(
    ! [A_60,A_61] :
      ( k3_xboole_0(A_60,A_61) = A_60
      | ~ r1_tarski(A_60,A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_323])).

tff(c_439,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_424])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_63,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ! [B_34,A_35] : r1_tarski(k3_xboole_0(B_34,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_63,c_10])).

tff(c_565,plain,(
    ! [B_66,A_67] : k3_xboole_0(k3_xboole_0(B_66,A_67),A_67) = k3_xboole_0(B_66,A_67) ),
    inference(resolution,[status(thm)],[c_78,c_424])).

tff(c_854,plain,(
    ! [A_75,B_76] : k3_xboole_0(k3_xboole_0(A_75,B_76),A_75) = k3_xboole_0(B_76,A_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_565])).

tff(c_926,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_854])).

tff(c_970,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_926])).

tff(c_24,plain,(
    ! [B_18,A_17] :
      ( k3_xboole_0(k1_relat_1(B_18),A_17) = k1_relat_1(k7_relat_1(B_18,A_17))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_994,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_970,c_24])).

tff(c_1027,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_994])).

tff(c_1047,plain,
    ( k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k7_relat_1('#skF_2','#skF_1')
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_176])).

tff(c_1368,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1047])).

tff(c_1371,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_12,c_1368])).

tff(c_1375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1371])).

tff(c_1377,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1047])).

tff(c_14,plain,(
    ! [A_9] :
      ( k9_relat_1(A_9,k1_relat_1(A_9)) = k2_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1053,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1027,c_14])).

tff(c_1879,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1053])).

tff(c_16,plain,(
    ! [A_10,C_14,B_13] :
      ( k9_relat_1(k7_relat_1(A_10,C_14),B_13) = k9_relat_1(A_10,B_13)
      | ~ r1_tarski(B_13,C_14)
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1883,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1879,c_16])).

tff(c_1890,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8,c_1883])).

tff(c_18,plain,(
    ! [A_15] :
      ( k10_relat_1(A_15,k2_relat_1(A_15)) = k1_relat_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1898,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1890,c_18])).

tff(c_1902,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1377,c_1027,c_1898])).

tff(c_368,plain,(
    ! [A_57,C_58,B_59] :
      ( k3_xboole_0(A_57,k10_relat_1(C_58,B_59)) = k10_relat_1(k7_relat_1(C_58,A_57),B_59)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_4152,plain,(
    ! [C_135,A_136,B_137] :
      ( r1_tarski(k10_relat_1(k7_relat_1(C_135,A_136),B_137),k10_relat_1(C_135,B_137))
      | ~ v1_relat_1(C_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_368,c_78])).

tff(c_4178,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1902,c_4152])).

tff(c_4213,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_4178])).

tff(c_4215,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_4213])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:33:06 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.49/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.88  
% 4.49/1.88  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.88  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 4.49/1.88  
% 4.49/1.88  %Foreground sorts:
% 4.49/1.88  
% 4.49/1.88  
% 4.49/1.88  %Background operators:
% 4.49/1.88  
% 4.49/1.88  
% 4.49/1.88  %Foreground operators:
% 4.49/1.88  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.49/1.88  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.49/1.88  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.49/1.88  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.49/1.88  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.49/1.88  tff('#skF_2', type, '#skF_2': $i).
% 4.49/1.88  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.49/1.88  tff('#skF_1', type, '#skF_1': $i).
% 4.49/1.88  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.49/1.88  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.49/1.88  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.49/1.88  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.49/1.88  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.49/1.88  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.49/1.88  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.49/1.88  
% 4.49/1.89  tff(f_83, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 4.49/1.89  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.49/1.89  tff(f_72, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 4.49/1.89  tff(f_58, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 4.49/1.89  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.49/1.89  tff(f_68, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 4.49/1.90  tff(f_62, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 4.49/1.90  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.49/1.90  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.49/1.90  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 4.49/1.90  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 4.49/1.90  tff(f_54, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 4.49/1.90  tff(f_76, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 4.49/1.90  tff(c_34, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.49/1.90  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.49/1.90  tff(c_12, plain, (![A_7, B_8]: (v1_relat_1(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.49/1.90  tff(c_28, plain, (![A_21]: (v1_relat_1(k6_relat_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.49/1.90  tff(c_20, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.49/1.90  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.49/1.90  tff(c_166, plain, (![B_43, A_44]: (k7_relat_1(B_43, A_44)=B_43 | ~r1_tarski(k1_relat_1(B_43), A_44) | ~v1_relat_1(B_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.49/1.90  tff(c_176, plain, (![B_43]: (k7_relat_1(B_43, k1_relat_1(B_43))=B_43 | ~v1_relat_1(B_43))), inference(resolution, [status(thm)], [c_8, c_166])).
% 4.49/1.90  tff(c_265, plain, (![B_52, A_53]: (k3_xboole_0(k1_relat_1(B_52), A_53)=k1_relat_1(k7_relat_1(B_52, A_53)) | ~v1_relat_1(B_52))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.49/1.90  tff(c_297, plain, (![A_16, A_53]: (k1_relat_1(k7_relat_1(k6_relat_1(A_16), A_53))=k3_xboole_0(A_16, A_53) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_265])).
% 4.49/1.90  tff(c_302, plain, (![A_54, A_55]: (k1_relat_1(k7_relat_1(k6_relat_1(A_54), A_55))=k3_xboole_0(A_54, A_55))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_297])).
% 4.49/1.90  tff(c_330, plain, (![A_54]: (k3_xboole_0(A_54, k1_relat_1(k6_relat_1(A_54)))=k1_relat_1(k6_relat_1(A_54)) | ~v1_relat_1(k6_relat_1(A_54)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_302])).
% 4.49/1.90  tff(c_336, plain, (![A_54]: (k3_xboole_0(A_54, A_54)=A_54)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_20, c_20, c_330])).
% 4.49/1.90  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.49/1.90  tff(c_169, plain, (![A_16, A_44]: (k7_relat_1(k6_relat_1(A_16), A_44)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_44) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_166])).
% 4.49/1.90  tff(c_175, plain, (![A_16, A_44]: (k7_relat_1(k6_relat_1(A_16), A_44)=k6_relat_1(A_16) | ~r1_tarski(A_16, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_169])).
% 4.49/1.90  tff(c_323, plain, (![A_16, A_44]: (k3_xboole_0(A_16, A_44)=k1_relat_1(k6_relat_1(A_16)) | ~r1_tarski(A_16, A_44))), inference(superposition, [status(thm), theory('equality')], [c_175, c_302])).
% 4.49/1.90  tff(c_424, plain, (![A_60, A_61]: (k3_xboole_0(A_60, A_61)=A_60 | ~r1_tarski(A_60, A_61))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_323])).
% 4.49/1.90  tff(c_439, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_36, c_424])).
% 4.49/1.90  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.49/1.90  tff(c_63, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.49/1.90  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.49/1.90  tff(c_78, plain, (![B_34, A_35]: (r1_tarski(k3_xboole_0(B_34, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_63, c_10])).
% 4.49/1.90  tff(c_565, plain, (![B_66, A_67]: (k3_xboole_0(k3_xboole_0(B_66, A_67), A_67)=k3_xboole_0(B_66, A_67))), inference(resolution, [status(thm)], [c_78, c_424])).
% 4.49/1.90  tff(c_854, plain, (![A_75, B_76]: (k3_xboole_0(k3_xboole_0(A_75, B_76), A_75)=k3_xboole_0(B_76, A_75))), inference(superposition, [status(thm), theory('equality')], [c_2, c_565])).
% 4.49/1.90  tff(c_926, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_439, c_854])).
% 4.49/1.90  tff(c_970, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_336, c_926])).
% 4.49/1.90  tff(c_24, plain, (![B_18, A_17]: (k3_xboole_0(k1_relat_1(B_18), A_17)=k1_relat_1(k7_relat_1(B_18, A_17)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.49/1.90  tff(c_994, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_970, c_24])).
% 4.49/1.90  tff(c_1027, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_994])).
% 4.49/1.90  tff(c_1047, plain, (k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k7_relat_1('#skF_2', '#skF_1') | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_176])).
% 4.49/1.90  tff(c_1368, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_1047])).
% 4.49/1.90  tff(c_1371, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_12, c_1368])).
% 4.49/1.90  tff(c_1375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1371])).
% 4.49/1.90  tff(c_1377, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_1047])).
% 4.49/1.90  tff(c_14, plain, (![A_9]: (k9_relat_1(A_9, k1_relat_1(A_9))=k2_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.49/1.90  tff(c_1053, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1027, c_14])).
% 4.49/1.90  tff(c_1879, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1053])).
% 4.49/1.90  tff(c_16, plain, (![A_10, C_14, B_13]: (k9_relat_1(k7_relat_1(A_10, C_14), B_13)=k9_relat_1(A_10, B_13) | ~r1_tarski(B_13, C_14) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.49/1.90  tff(c_1883, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1879, c_16])).
% 4.49/1.90  tff(c_1890, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8, c_1883])).
% 4.49/1.90  tff(c_18, plain, (![A_15]: (k10_relat_1(A_15, k2_relat_1(A_15))=k1_relat_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.49/1.90  tff(c_1898, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1890, c_18])).
% 4.49/1.90  tff(c_1902, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1377, c_1027, c_1898])).
% 4.49/1.90  tff(c_368, plain, (![A_57, C_58, B_59]: (k3_xboole_0(A_57, k10_relat_1(C_58, B_59))=k10_relat_1(k7_relat_1(C_58, A_57), B_59) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.49/1.90  tff(c_4152, plain, (![C_135, A_136, B_137]: (r1_tarski(k10_relat_1(k7_relat_1(C_135, A_136), B_137), k10_relat_1(C_135, B_137)) | ~v1_relat_1(C_135))), inference(superposition, [status(thm), theory('equality')], [c_368, c_78])).
% 4.49/1.90  tff(c_4178, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1902, c_4152])).
% 4.49/1.90  tff(c_4213, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_4178])).
% 4.49/1.90  tff(c_4215, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_4213])).
% 4.49/1.90  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.49/1.90  
% 4.49/1.90  Inference rules
% 4.49/1.90  ----------------------
% 4.49/1.90  #Ref     : 0
% 4.49/1.90  #Sup     : 1003
% 4.49/1.90  #Fact    : 0
% 4.49/1.90  #Define  : 0
% 4.49/1.90  #Split   : 3
% 4.49/1.90  #Chain   : 0
% 4.49/1.90  #Close   : 0
% 4.49/1.90  
% 4.49/1.90  Ordering : KBO
% 4.49/1.90  
% 4.49/1.90  Simplification rules
% 4.49/1.90  ----------------------
% 4.49/1.90  #Subsume      : 137
% 4.49/1.90  #Demod        : 1192
% 4.49/1.90  #Tautology    : 565
% 4.49/1.90  #SimpNegUnit  : 1
% 4.49/1.90  #BackRed      : 2
% 4.49/1.90  
% 4.49/1.90  #Partial instantiations: 0
% 4.49/1.90  #Strategies tried      : 1
% 4.49/1.90  
% 4.49/1.90  Timing (in seconds)
% 4.49/1.90  ----------------------
% 4.49/1.90  Preprocessing        : 0.30
% 4.49/1.90  Parsing              : 0.16
% 4.49/1.90  CNF conversion       : 0.02
% 4.49/1.90  Main loop            : 0.77
% 4.49/1.90  Inferencing          : 0.24
% 4.49/1.90  Reduction            : 0.34
% 4.49/1.90  Demodulation         : 0.28
% 4.49/1.90  BG Simplification    : 0.03
% 4.49/1.90  Subsumption          : 0.13
% 4.49/1.90  Abstraction          : 0.05
% 4.49/1.90  MUC search           : 0.00
% 4.49/1.90  Cooper               : 0.00
% 4.49/1.90  Total                : 1.10
% 4.49/1.90  Index Insertion      : 0.00
% 4.49/1.90  Index Deletion       : 0.00
% 4.49/1.90  Index Matching       : 0.00
% 4.49/1.90  BG Taut test         : 0.00
%------------------------------------------------------------------------------
