%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 3.01s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   72 (  96 expanded)
%              Number of leaves         :   29 (  44 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 145 expanded)
%              Number of equality atoms :   34 (  52 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

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

tff(f_85,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_65,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_61,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => r1_tarski(k9_relat_1(B,k10_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t145_funct_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_34,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_40,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_36,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_26,plain,(
    ! [A_17] : v1_relat_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_24,plain,(
    ! [A_16] : k2_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_22,plain,(
    ! [A_16] : k1_relat_1(k6_relat_1(A_16)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_138,plain,(
    ! [A_40] :
      ( k9_relat_1(A_40,k1_relat_1(A_40)) = k2_relat_1(A_40)
      | ~ v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_147,plain,(
    ! [A_16] :
      ( k9_relat_1(k6_relat_1(A_16),A_16) = k2_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_138])).

tff(c_151,plain,(
    ! [A_16] : k9_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_24,c_147])).

tff(c_165,plain,(
    ! [A_44] :
      ( k10_relat_1(A_44,k2_relat_1(A_44)) = k1_relat_1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_181,plain,(
    ! [A_16] :
      ( k10_relat_1(k6_relat_1(A_16),A_16) = k1_relat_1(k6_relat_1(A_16))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_165])).

tff(c_188,plain,(
    ! [A_16] : k10_relat_1(k6_relat_1(A_16),A_16) = A_16 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22,c_181])).

tff(c_567,plain,(
    ! [C_74,A_75,B_76] :
      ( r1_tarski(k10_relat_1(C_74,A_75),k10_relat_1(C_74,B_76))
      | ~ r1_tarski(A_75,B_76)
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_602,plain,(
    ! [A_16,B_76] :
      ( r1_tarski(A_16,k10_relat_1(k6_relat_1(A_16),B_76))
      | ~ r1_tarski(A_16,B_76)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_567])).

tff(c_625,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(A_77,k10_relat_1(k6_relat_1(A_77),B_78))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_602])).

tff(c_129,plain,(
    ! [B_38,A_39] :
      ( r1_tarski(k10_relat_1(B_38,A_39),k1_relat_1(B_38))
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_134,plain,(
    ! [A_16,A_39] :
      ( r1_tarski(k10_relat_1(k6_relat_1(A_16),A_39),A_16)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_129])).

tff(c_161,plain,(
    ! [A_42,A_43] : r1_tarski(k10_relat_1(k6_relat_1(A_42),A_43),A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_134])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_164,plain,(
    ! [A_42,A_43] :
      ( k10_relat_1(k6_relat_1(A_42),A_43) = A_42
      | ~ r1_tarski(A_42,k10_relat_1(k6_relat_1(A_42),A_43)) ) ),
    inference(resolution,[status(thm)],[c_161,c_4])).

tff(c_652,plain,(
    ! [A_77,B_78] :
      ( k10_relat_1(k6_relat_1(A_77),B_78) = A_77
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_625,c_164])).

tff(c_28,plain,(
    ! [A_17] : v1_funct_1(k6_relat_1(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_248,plain,(
    ! [B_56,A_57] :
      ( k10_relat_1(B_56,k3_xboole_0(k2_relat_1(B_56),A_57)) = k10_relat_1(B_56,A_57)
      | ~ v1_relat_1(B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_275,plain,(
    ! [A_16,A_57] :
      ( k10_relat_1(k6_relat_1(A_16),k3_xboole_0(A_16,A_57)) = k10_relat_1(k6_relat_1(A_16),A_57)
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_248])).

tff(c_282,plain,(
    ! [A_58,A_59] : k10_relat_1(k6_relat_1(A_58),k3_xboole_0(A_58,A_59)) = k10_relat_1(k6_relat_1(A_58),A_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_275])).

tff(c_32,plain,(
    ! [B_22,A_21] :
      ( r1_tarski(k9_relat_1(B_22,k10_relat_1(B_22,A_21)),A_21)
      | ~ v1_funct_1(B_22)
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_288,plain,(
    ! [A_58,A_59] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_58),k10_relat_1(k6_relat_1(A_58),A_59)),k3_xboole_0(A_58,A_59))
      | ~ v1_funct_1(k6_relat_1(A_58))
      | ~ v1_relat_1(k6_relat_1(A_58)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_282,c_32])).

tff(c_944,plain,(
    ! [A_91,A_92] : r1_tarski(k9_relat_1(k6_relat_1(A_91),k10_relat_1(k6_relat_1(A_91),A_92)),k3_xboole_0(A_91,A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_28,c_288])).

tff(c_952,plain,(
    ! [A_77,B_78] :
      ( r1_tarski(k9_relat_1(k6_relat_1(A_77),A_77),k3_xboole_0(A_77,B_78))
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_944])).

tff(c_1124,plain,(
    ! [A_95,B_96] :
      ( r1_tarski(A_95,k3_xboole_0(A_95,B_96))
      | ~ r1_tarski(A_95,B_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_952])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_64,plain,(
    ! [B_32,A_33] : k3_xboole_0(B_32,A_33) = k3_xboole_0(A_33,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_79,plain,(
    ! [B_32,A_33] : r1_tarski(k3_xboole_0(B_32,A_33),A_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_10])).

tff(c_113,plain,(
    ! [B_36,A_37] :
      ( B_36 = A_37
      | ~ r1_tarski(B_36,A_37)
      | ~ r1_tarski(A_37,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    ! [B_48,A_49] :
      ( k3_xboole_0(B_48,A_49) = A_49
      | ~ r1_tarski(A_49,k3_xboole_0(B_48,A_49)) ) ),
    inference(resolution,[status(thm)],[c_79,c_113])).

tff(c_218,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(B_2,k3_xboole_0(B_2,A_1)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_1180,plain,(
    ! [B_97,A_98] :
      ( k3_xboole_0(B_97,A_98) = A_98
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(resolution,[status(thm)],[c_1124,c_218])).

tff(c_1233,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_1180])).

tff(c_30,plain,(
    ! [A_18,C_20,B_19] :
      ( k3_xboole_0(A_18,k10_relat_1(C_20,B_19)) = k10_relat_1(k7_relat_1(C_20,A_18),B_19)
      | ~ v1_relat_1(C_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1309,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1233,c_30])).

tff(c_1343,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1309])).

tff(c_1345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_1343])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:02:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.01/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.45  
% 3.01/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.01/1.45  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 3.01/1.45  
% 3.01/1.45  %Foreground sorts:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Background operators:
% 3.01/1.45  
% 3.01/1.45  
% 3.01/1.45  %Foreground operators:
% 3.01/1.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.01/1.45  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.01/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.01/1.45  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.01/1.45  tff('#skF_2', type, '#skF_2': $i).
% 3.01/1.45  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.01/1.45  tff('#skF_3', type, '#skF_3': $i).
% 3.01/1.45  tff('#skF_1', type, '#skF_1': $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.01/1.45  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.01/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.01/1.45  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.01/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.01/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.01/1.45  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.01/1.45  
% 3.15/1.47  tff(f_85, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.15/1.47  tff(f_65, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.15/1.47  tff(f_61, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.15/1.47  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_relat_1)).
% 3.15/1.47  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 3.15/1.47  tff(f_57, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 3.15/1.47  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 3.15/1.47  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.47  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 3.15/1.47  tff(f_75, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => r1_tarski(k9_relat_1(B, k10_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t145_funct_1)).
% 3.15/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.47  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.15/1.47  tff(f_69, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.15/1.47  tff(c_34, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.47  tff(c_40, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.47  tff(c_36, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.15/1.47  tff(c_26, plain, (![A_17]: (v1_relat_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.47  tff(c_24, plain, (![A_16]: (k2_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.47  tff(c_22, plain, (![A_16]: (k1_relat_1(k6_relat_1(A_16))=A_16)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.15/1.47  tff(c_138, plain, (![A_40]: (k9_relat_1(A_40, k1_relat_1(A_40))=k2_relat_1(A_40) | ~v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.47  tff(c_147, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=k2_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_138])).
% 3.15/1.47  tff(c_151, plain, (![A_16]: (k9_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_24, c_147])).
% 3.15/1.47  tff(c_165, plain, (![A_44]: (k10_relat_1(A_44, k2_relat_1(A_44))=k1_relat_1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.15/1.47  tff(c_181, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=k1_relat_1(k6_relat_1(A_16)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_165])).
% 3.15/1.47  tff(c_188, plain, (![A_16]: (k10_relat_1(k6_relat_1(A_16), A_16)=A_16)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22, c_181])).
% 3.15/1.47  tff(c_567, plain, (![C_74, A_75, B_76]: (r1_tarski(k10_relat_1(C_74, A_75), k10_relat_1(C_74, B_76)) | ~r1_tarski(A_75, B_76) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.15/1.47  tff(c_602, plain, (![A_16, B_76]: (r1_tarski(A_16, k10_relat_1(k6_relat_1(A_16), B_76)) | ~r1_tarski(A_16, B_76) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_567])).
% 3.15/1.47  tff(c_625, plain, (![A_77, B_78]: (r1_tarski(A_77, k10_relat_1(k6_relat_1(A_77), B_78)) | ~r1_tarski(A_77, B_78))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_602])).
% 3.15/1.47  tff(c_129, plain, (![B_38, A_39]: (r1_tarski(k10_relat_1(B_38, A_39), k1_relat_1(B_38)) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.47  tff(c_134, plain, (![A_16, A_39]: (r1_tarski(k10_relat_1(k6_relat_1(A_16), A_39), A_16) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_129])).
% 3.15/1.47  tff(c_161, plain, (![A_42, A_43]: (r1_tarski(k10_relat_1(k6_relat_1(A_42), A_43), A_42))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_134])).
% 3.15/1.47  tff(c_4, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_164, plain, (![A_42, A_43]: (k10_relat_1(k6_relat_1(A_42), A_43)=A_42 | ~r1_tarski(A_42, k10_relat_1(k6_relat_1(A_42), A_43)))), inference(resolution, [status(thm)], [c_161, c_4])).
% 3.15/1.47  tff(c_652, plain, (![A_77, B_78]: (k10_relat_1(k6_relat_1(A_77), B_78)=A_77 | ~r1_tarski(A_77, B_78))), inference(resolution, [status(thm)], [c_625, c_164])).
% 3.15/1.47  tff(c_28, plain, (![A_17]: (v1_funct_1(k6_relat_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.47  tff(c_248, plain, (![B_56, A_57]: (k10_relat_1(B_56, k3_xboole_0(k2_relat_1(B_56), A_57))=k10_relat_1(B_56, A_57) | ~v1_relat_1(B_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.15/1.47  tff(c_275, plain, (![A_16, A_57]: (k10_relat_1(k6_relat_1(A_16), k3_xboole_0(A_16, A_57))=k10_relat_1(k6_relat_1(A_16), A_57) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_248])).
% 3.15/1.47  tff(c_282, plain, (![A_58, A_59]: (k10_relat_1(k6_relat_1(A_58), k3_xboole_0(A_58, A_59))=k10_relat_1(k6_relat_1(A_58), A_59))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_275])).
% 3.15/1.47  tff(c_32, plain, (![B_22, A_21]: (r1_tarski(k9_relat_1(B_22, k10_relat_1(B_22, A_21)), A_21) | ~v1_funct_1(B_22) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.15/1.47  tff(c_288, plain, (![A_58, A_59]: (r1_tarski(k9_relat_1(k6_relat_1(A_58), k10_relat_1(k6_relat_1(A_58), A_59)), k3_xboole_0(A_58, A_59)) | ~v1_funct_1(k6_relat_1(A_58)) | ~v1_relat_1(k6_relat_1(A_58)))), inference(superposition, [status(thm), theory('equality')], [c_282, c_32])).
% 3.15/1.47  tff(c_944, plain, (![A_91, A_92]: (r1_tarski(k9_relat_1(k6_relat_1(A_91), k10_relat_1(k6_relat_1(A_91), A_92)), k3_xboole_0(A_91, A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_28, c_288])).
% 3.15/1.47  tff(c_952, plain, (![A_77, B_78]: (r1_tarski(k9_relat_1(k6_relat_1(A_77), A_77), k3_xboole_0(A_77, B_78)) | ~r1_tarski(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_652, c_944])).
% 3.15/1.47  tff(c_1124, plain, (![A_95, B_96]: (r1_tarski(A_95, k3_xboole_0(A_95, B_96)) | ~r1_tarski(A_95, B_96))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_952])).
% 3.15/1.47  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_64, plain, (![B_32, A_33]: (k3_xboole_0(B_32, A_33)=k3_xboole_0(A_33, B_32))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.47  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.47  tff(c_79, plain, (![B_32, A_33]: (r1_tarski(k3_xboole_0(B_32, A_33), A_33))), inference(superposition, [status(thm), theory('equality')], [c_64, c_10])).
% 3.15/1.47  tff(c_113, plain, (![B_36, A_37]: (B_36=A_37 | ~r1_tarski(B_36, A_37) | ~r1_tarski(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.47  tff(c_215, plain, (![B_48, A_49]: (k3_xboole_0(B_48, A_49)=A_49 | ~r1_tarski(A_49, k3_xboole_0(B_48, A_49)))), inference(resolution, [status(thm)], [c_79, c_113])).
% 3.15/1.47  tff(c_218, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(B_2, k3_xboole_0(B_2, A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 3.15/1.47  tff(c_1180, plain, (![B_97, A_98]: (k3_xboole_0(B_97, A_98)=A_98 | ~r1_tarski(A_98, B_97))), inference(resolution, [status(thm)], [c_1124, c_218])).
% 3.15/1.47  tff(c_1233, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_36, c_1180])).
% 3.15/1.47  tff(c_30, plain, (![A_18, C_20, B_19]: (k3_xboole_0(A_18, k10_relat_1(C_20, B_19))=k10_relat_1(k7_relat_1(C_20, A_18), B_19) | ~v1_relat_1(C_20))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.15/1.47  tff(c_1309, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1233, c_30])).
% 3.15/1.47  tff(c_1343, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1309])).
% 3.15/1.47  tff(c_1345, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_1343])).
% 3.15/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.47  
% 3.15/1.47  Inference rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Ref     : 0
% 3.15/1.47  #Sup     : 308
% 3.15/1.47  #Fact    : 0
% 3.15/1.47  #Define  : 0
% 3.15/1.47  #Split   : 1
% 3.15/1.47  #Chain   : 0
% 3.15/1.47  #Close   : 0
% 3.15/1.47  
% 3.15/1.47  Ordering : KBO
% 3.15/1.47  
% 3.15/1.47  Simplification rules
% 3.15/1.47  ----------------------
% 3.15/1.47  #Subsume      : 42
% 3.15/1.47  #Demod        : 201
% 3.15/1.47  #Tautology    : 111
% 3.15/1.47  #SimpNegUnit  : 2
% 3.15/1.47  #BackRed      : 1
% 3.15/1.47  
% 3.15/1.47  #Partial instantiations: 0
% 3.15/1.47  #Strategies tried      : 1
% 3.15/1.47  
% 3.15/1.47  Timing (in seconds)
% 3.15/1.47  ----------------------
% 3.15/1.47  Preprocessing        : 0.30
% 3.15/1.47  Parsing              : 0.16
% 3.15/1.47  CNF conversion       : 0.02
% 3.15/1.47  Main loop            : 0.41
% 3.15/1.47  Inferencing          : 0.14
% 3.15/1.47  Reduction            : 0.14
% 3.15/1.47  Demodulation         : 0.11
% 3.15/1.47  BG Simplification    : 0.02
% 3.15/1.47  Subsumption          : 0.07
% 3.15/1.47  Abstraction          : 0.02
% 3.15/1.47  MUC search           : 0.00
% 3.15/1.47  Cooper               : 0.00
% 3.15/1.48  Total                : 0.74
% 3.15/1.48  Index Insertion      : 0.00
% 3.15/1.48  Index Deletion       : 0.00
% 3.15/1.48  Index Matching       : 0.00
% 3.15/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
