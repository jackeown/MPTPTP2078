%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:40 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 4.85s
% Verified   : 
% Statistics : Number of formulae       :   71 (  90 expanded)
%              Number of leaves         :   32 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  112 ( 154 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v4_relat_1 > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k2_wellord1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_wellord1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k3_relat_1(k2_wellord1(B,A)),k3_relat_1(B))
        & r1_tarski(k3_relat_1(k2_wellord1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_wellord1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_relat_1(A) = k2_xboole_0(k1_relat_1(A),k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(B,A) = k7_relat_1(k8_relat_1(A,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_wellord1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_22,plain,(
    ! [A_20,B_21] :
      ( v1_relat_1(k2_wellord1(A_20,B_21))
      | ~ v1_relat_1(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_26,plain,(
    ! [B_25,A_24] :
      ( r1_tarski(k3_relat_1(k2_wellord1(B_25,A_24)),A_24)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_206,plain,(
    ! [A_59] :
      ( k2_xboole_0(k1_relat_1(A_59),k2_relat_1(A_59)) = k3_relat_1(A_59)
      | ~ v1_relat_1(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(B_38,A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_71])).

tff(c_10,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_101,plain,(
    ! [B_38,A_37] : k2_xboole_0(B_38,A_37) = k2_xboole_0(A_37,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_10])).

tff(c_153,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_tarski(A_43,C_44)
      | ~ r1_tarski(k2_xboole_0(A_43,B_45),C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_156,plain,(
    ! [A_37,C_44,B_38] :
      ( r1_tarski(A_37,C_44)
      | ~ r1_tarski(k2_xboole_0(B_38,A_37),C_44) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_153])).

tff(c_392,plain,(
    ! [A_82,C_83] :
      ( r1_tarski(k2_relat_1(A_82),C_83)
      | ~ r1_tarski(k3_relat_1(A_82),C_83)
      | ~ v1_relat_1(A_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_156])).

tff(c_666,plain,(
    ! [B_112,A_113] :
      ( r1_tarski(k2_relat_1(k2_wellord1(B_112,A_113)),A_113)
      | ~ v1_relat_1(k2_wellord1(B_112,A_113))
      | ~ v1_relat_1(B_112) ) ),
    inference(resolution,[status(thm)],[c_26,c_392])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_168,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,C_52)
      | ~ r1_tarski(B_53,C_52)
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,'#skF_2')
      | ~ r1_tarski(A_51,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_34,c_168])).

tff(c_277,plain,(
    ! [A_72,B_73] :
      ( k8_relat_1(A_72,B_73) = B_73
      | ~ r1_tarski(k2_relat_1(B_73),A_72)
      | ~ v1_relat_1(B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_282,plain,(
    ! [B_73] :
      ( k8_relat_1('#skF_2',B_73) = B_73
      | ~ v1_relat_1(B_73)
      | ~ r1_tarski(k2_relat_1(B_73),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_177,c_277])).

tff(c_774,plain,(
    ! [B_118] :
      ( k8_relat_1('#skF_2',k2_wellord1(B_118,'#skF_1')) = k2_wellord1(B_118,'#skF_1')
      | ~ v1_relat_1(k2_wellord1(B_118,'#skF_1'))
      | ~ v1_relat_1(B_118) ) ),
    inference(resolution,[status(thm)],[c_666,c_282])).

tff(c_793,plain,(
    ! [A_119] :
      ( k8_relat_1('#skF_2',k2_wellord1(A_119,'#skF_1')) = k2_wellord1(A_119,'#skF_1')
      | ~ v1_relat_1(A_119) ) ),
    inference(resolution,[status(thm)],[c_22,c_774])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k7_relat_1(k8_relat_1(A_22,B_23),A_22) = k2_wellord1(B_23,A_22)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_2632,plain,(
    ! [A_217] :
      ( k7_relat_1(k2_wellord1(A_217,'#skF_1'),'#skF_2') = k2_wellord1(k2_wellord1(A_217,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(k2_wellord1(A_217,'#skF_1'))
      | ~ v1_relat_1(A_217) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_793,c_24])).

tff(c_2659,plain,(
    ! [A_218] :
      ( k7_relat_1(k2_wellord1(A_218,'#skF_1'),'#skF_2') = k2_wellord1(k2_wellord1(A_218,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(A_218) ) ),
    inference(resolution,[status(thm)],[c_22,c_2632])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_292,plain,(
    ! [A_76,C_77] :
      ( r1_tarski(k1_relat_1(A_76),C_77)
      | ~ r1_tarski(k3_relat_1(A_76),C_77)
      | ~ v1_relat_1(A_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_499,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(k1_relat_1(k2_wellord1(B_99,A_100)),A_100)
      | ~ v1_relat_1(k2_wellord1(B_99,A_100))
      | ~ v1_relat_1(B_99) ) ),
    inference(resolution,[status(thm)],[c_26,c_292])).

tff(c_232,plain,(
    ! [B_64,A_65] :
      ( v4_relat_1(B_64,A_65)
      | ~ r1_tarski(k1_relat_1(B_64),A_65)
      | ~ v1_relat_1(B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_240,plain,(
    ! [B_64] :
      ( v4_relat_1(B_64,'#skF_2')
      | ~ v1_relat_1(B_64)
      | ~ r1_tarski(k1_relat_1(B_64),'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_177,c_232])).

tff(c_535,plain,(
    ! [B_101] :
      ( v4_relat_1(k2_wellord1(B_101,'#skF_1'),'#skF_2')
      | ~ v1_relat_1(k2_wellord1(B_101,'#skF_1'))
      | ~ v1_relat_1(B_101) ) ),
    inference(resolution,[status(thm)],[c_499,c_240])).

tff(c_20,plain,(
    ! [B_19,A_18] :
      ( k7_relat_1(B_19,A_18) = B_19
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1144,plain,(
    ! [B_146] :
      ( k7_relat_1(k2_wellord1(B_146,'#skF_1'),'#skF_2') = k2_wellord1(B_146,'#skF_1')
      | ~ v1_relat_1(k2_wellord1(B_146,'#skF_1'))
      | ~ v1_relat_1(B_146) ) ),
    inference(resolution,[status(thm)],[c_535,c_20])).

tff(c_1162,plain,(
    ! [A_20] :
      ( k7_relat_1(k2_wellord1(A_20,'#skF_1'),'#skF_2') = k2_wellord1(A_20,'#skF_1')
      | ~ v1_relat_1(A_20) ) ),
    inference(resolution,[status(thm)],[c_22,c_1144])).

tff(c_2709,plain,(
    ! [A_222] :
      ( k2_wellord1(k2_wellord1(A_222,'#skF_1'),'#skF_2') = k2_wellord1(A_222,'#skF_1')
      | ~ v1_relat_1(A_222)
      | ~ v1_relat_1(A_222) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2659,c_1162])).

tff(c_307,plain,(
    ! [C_79,B_80,A_81] :
      ( k2_wellord1(k2_wellord1(C_79,B_80),A_81) = k2_wellord1(k2_wellord1(C_79,A_81),B_80)
      | ~ v1_relat_1(C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_32,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_346,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_307,c_32])).

tff(c_385,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_346])).

tff(c_2873,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_2709,c_385])).

tff(c_2920,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_2873])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:13:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.87  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.87  
% 4.85/1.87  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.87  %$ v4_relat_1 > r1_tarski > v1_relat_1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k3_relat_1 > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 4.85/1.87  
% 4.85/1.87  %Foreground sorts:
% 4.85/1.87  
% 4.85/1.87  
% 4.85/1.87  %Background operators:
% 4.85/1.87  
% 4.85/1.87  
% 4.85/1.87  %Foreground operators:
% 4.85/1.87  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 4.85/1.87  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.85/1.87  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.85/1.87  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 4.85/1.87  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.85/1.87  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.85/1.87  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.85/1.87  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.85/1.87  tff('#skF_2', type, '#skF_2': $i).
% 4.85/1.87  tff('#skF_3', type, '#skF_3': $i).
% 4.85/1.87  tff('#skF_1', type, '#skF_1': $i).
% 4.85/1.87  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.85/1.87  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.85/1.87  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.85/1.87  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.85/1.87  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.85/1.87  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.85/1.87  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 4.85/1.87  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.85/1.87  
% 4.85/1.89  tff(f_88, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 4.85/1.89  tff(f_67, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k2_wellord1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_wellord1)).
% 4.85/1.89  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k3_relat_1(k2_wellord1(B, A)), k3_relat_1(B)) & r1_tarski(k3_relat_1(k2_wellord1(B, A)), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_wellord1)).
% 4.85/1.89  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (k3_relat_1(A) = k2_xboole_0(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_relat_1)).
% 4.85/1.89  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.85/1.89  tff(f_41, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.85/1.89  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 4.85/1.89  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.85/1.89  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 4.85/1.89  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(B, A) = k7_relat_1(k8_relat_1(A, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_wellord1)).
% 4.85/1.89  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 4.85/1.89  tff(f_63, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 4.85/1.89  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 4.85/1.89  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.85/1.89  tff(c_22, plain, (![A_20, B_21]: (v1_relat_1(k2_wellord1(A_20, B_21)) | ~v1_relat_1(A_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.85/1.89  tff(c_26, plain, (![B_25, A_24]: (r1_tarski(k3_relat_1(k2_wellord1(B_25, A_24)), A_24) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.85/1.89  tff(c_206, plain, (![A_59]: (k2_xboole_0(k1_relat_1(A_59), k2_relat_1(A_59))=k3_relat_1(A_59) | ~v1_relat_1(A_59))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.85/1.89  tff(c_6, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.85/1.89  tff(c_71, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/1.89  tff(c_95, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(B_38, A_37))), inference(superposition, [status(thm), theory('equality')], [c_6, c_71])).
% 4.85/1.89  tff(c_10, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.85/1.89  tff(c_101, plain, (![B_38, A_37]: (k2_xboole_0(B_38, A_37)=k2_xboole_0(A_37, B_38))), inference(superposition, [status(thm), theory('equality')], [c_95, c_10])).
% 4.85/1.89  tff(c_153, plain, (![A_43, C_44, B_45]: (r1_tarski(A_43, C_44) | ~r1_tarski(k2_xboole_0(A_43, B_45), C_44))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/1.89  tff(c_156, plain, (![A_37, C_44, B_38]: (r1_tarski(A_37, C_44) | ~r1_tarski(k2_xboole_0(B_38, A_37), C_44))), inference(superposition, [status(thm), theory('equality')], [c_101, c_153])).
% 4.85/1.89  tff(c_392, plain, (![A_82, C_83]: (r1_tarski(k2_relat_1(A_82), C_83) | ~r1_tarski(k3_relat_1(A_82), C_83) | ~v1_relat_1(A_82))), inference(superposition, [status(thm), theory('equality')], [c_206, c_156])).
% 4.85/1.89  tff(c_666, plain, (![B_112, A_113]: (r1_tarski(k2_relat_1(k2_wellord1(B_112, A_113)), A_113) | ~v1_relat_1(k2_wellord1(B_112, A_113)) | ~v1_relat_1(B_112))), inference(resolution, [status(thm)], [c_26, c_392])).
% 4.85/1.89  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.85/1.89  tff(c_168, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, C_52) | ~r1_tarski(B_53, C_52) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.85/1.89  tff(c_177, plain, (![A_51]: (r1_tarski(A_51, '#skF_2') | ~r1_tarski(A_51, '#skF_1'))), inference(resolution, [status(thm)], [c_34, c_168])).
% 4.85/1.89  tff(c_277, plain, (![A_72, B_73]: (k8_relat_1(A_72, B_73)=B_73 | ~r1_tarski(k2_relat_1(B_73), A_72) | ~v1_relat_1(B_73))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.85/1.89  tff(c_282, plain, (![B_73]: (k8_relat_1('#skF_2', B_73)=B_73 | ~v1_relat_1(B_73) | ~r1_tarski(k2_relat_1(B_73), '#skF_1'))), inference(resolution, [status(thm)], [c_177, c_277])).
% 4.85/1.89  tff(c_774, plain, (![B_118]: (k8_relat_1('#skF_2', k2_wellord1(B_118, '#skF_1'))=k2_wellord1(B_118, '#skF_1') | ~v1_relat_1(k2_wellord1(B_118, '#skF_1')) | ~v1_relat_1(B_118))), inference(resolution, [status(thm)], [c_666, c_282])).
% 4.85/1.89  tff(c_793, plain, (![A_119]: (k8_relat_1('#skF_2', k2_wellord1(A_119, '#skF_1'))=k2_wellord1(A_119, '#skF_1') | ~v1_relat_1(A_119))), inference(resolution, [status(thm)], [c_22, c_774])).
% 4.85/1.89  tff(c_24, plain, (![A_22, B_23]: (k7_relat_1(k8_relat_1(A_22, B_23), A_22)=k2_wellord1(B_23, A_22) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.85/1.89  tff(c_2632, plain, (![A_217]: (k7_relat_1(k2_wellord1(A_217, '#skF_1'), '#skF_2')=k2_wellord1(k2_wellord1(A_217, '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1(A_217, '#skF_1')) | ~v1_relat_1(A_217))), inference(superposition, [status(thm), theory('equality')], [c_793, c_24])).
% 4.85/1.89  tff(c_2659, plain, (![A_218]: (k7_relat_1(k2_wellord1(A_218, '#skF_1'), '#skF_2')=k2_wellord1(k2_wellord1(A_218, '#skF_1'), '#skF_2') | ~v1_relat_1(A_218))), inference(resolution, [status(thm)], [c_22, c_2632])).
% 4.85/1.89  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.85/1.89  tff(c_292, plain, (![A_76, C_77]: (r1_tarski(k1_relat_1(A_76), C_77) | ~r1_tarski(k3_relat_1(A_76), C_77) | ~v1_relat_1(A_76))), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 4.85/1.89  tff(c_499, plain, (![B_99, A_100]: (r1_tarski(k1_relat_1(k2_wellord1(B_99, A_100)), A_100) | ~v1_relat_1(k2_wellord1(B_99, A_100)) | ~v1_relat_1(B_99))), inference(resolution, [status(thm)], [c_26, c_292])).
% 4.85/1.89  tff(c_232, plain, (![B_64, A_65]: (v4_relat_1(B_64, A_65) | ~r1_tarski(k1_relat_1(B_64), A_65) | ~v1_relat_1(B_64))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.85/1.89  tff(c_240, plain, (![B_64]: (v4_relat_1(B_64, '#skF_2') | ~v1_relat_1(B_64) | ~r1_tarski(k1_relat_1(B_64), '#skF_1'))), inference(resolution, [status(thm)], [c_177, c_232])).
% 4.85/1.89  tff(c_535, plain, (![B_101]: (v4_relat_1(k2_wellord1(B_101, '#skF_1'), '#skF_2') | ~v1_relat_1(k2_wellord1(B_101, '#skF_1')) | ~v1_relat_1(B_101))), inference(resolution, [status(thm)], [c_499, c_240])).
% 4.85/1.89  tff(c_20, plain, (![B_19, A_18]: (k7_relat_1(B_19, A_18)=B_19 | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.85/1.89  tff(c_1144, plain, (![B_146]: (k7_relat_1(k2_wellord1(B_146, '#skF_1'), '#skF_2')=k2_wellord1(B_146, '#skF_1') | ~v1_relat_1(k2_wellord1(B_146, '#skF_1')) | ~v1_relat_1(B_146))), inference(resolution, [status(thm)], [c_535, c_20])).
% 4.85/1.89  tff(c_1162, plain, (![A_20]: (k7_relat_1(k2_wellord1(A_20, '#skF_1'), '#skF_2')=k2_wellord1(A_20, '#skF_1') | ~v1_relat_1(A_20))), inference(resolution, [status(thm)], [c_22, c_1144])).
% 4.85/1.89  tff(c_2709, plain, (![A_222]: (k2_wellord1(k2_wellord1(A_222, '#skF_1'), '#skF_2')=k2_wellord1(A_222, '#skF_1') | ~v1_relat_1(A_222) | ~v1_relat_1(A_222))), inference(superposition, [status(thm), theory('equality')], [c_2659, c_1162])).
% 4.85/1.89  tff(c_307, plain, (![C_79, B_80, A_81]: (k2_wellord1(k2_wellord1(C_79, B_80), A_81)=k2_wellord1(k2_wellord1(C_79, A_81), B_80) | ~v1_relat_1(C_79))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.85/1.89  tff(c_32, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.85/1.89  tff(c_346, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_307, c_32])).
% 4.85/1.89  tff(c_385, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_346])).
% 4.85/1.89  tff(c_2873, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_2709, c_385])).
% 4.85/1.89  tff(c_2920, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_2873])).
% 4.85/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.85/1.89  
% 4.85/1.89  Inference rules
% 4.85/1.89  ----------------------
% 4.85/1.89  #Ref     : 0
% 4.85/1.89  #Sup     : 756
% 4.85/1.89  #Fact    : 0
% 4.85/1.89  #Define  : 0
% 4.85/1.89  #Split   : 1
% 4.85/1.89  #Chain   : 0
% 4.85/1.89  #Close   : 0
% 4.85/1.89  
% 4.85/1.89  Ordering : KBO
% 4.85/1.89  
% 4.85/1.89  Simplification rules
% 4.85/1.89  ----------------------
% 4.85/1.89  #Subsume      : 92
% 4.85/1.89  #Demod        : 7
% 4.85/1.89  #Tautology    : 63
% 4.85/1.89  #SimpNegUnit  : 0
% 4.85/1.89  #BackRed      : 0
% 4.85/1.89  
% 4.85/1.89  #Partial instantiations: 0
% 4.85/1.89  #Strategies tried      : 1
% 4.85/1.89  
% 4.85/1.89  Timing (in seconds)
% 4.85/1.89  ----------------------
% 4.85/1.89  Preprocessing        : 0.30
% 4.85/1.89  Parsing              : 0.16
% 4.85/1.89  CNF conversion       : 0.02
% 4.85/1.89  Main loop            : 0.82
% 4.85/1.89  Inferencing          : 0.29
% 4.85/1.89  Reduction            : 0.19
% 4.85/1.89  Demodulation         : 0.13
% 4.85/1.89  BG Simplification    : 0.04
% 4.85/1.89  Subsumption          : 0.25
% 4.85/1.89  Abstraction          : 0.04
% 4.85/1.89  MUC search           : 0.00
% 4.85/1.89  Cooper               : 0.00
% 4.85/1.89  Total                : 1.15
% 4.85/1.89  Index Insertion      : 0.00
% 4.85/1.89  Index Deletion       : 0.00
% 4.85/1.89  Index Matching       : 0.00
% 4.85/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
