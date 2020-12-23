%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:43 EST 2020

% Result     : Theorem 41.85s
% Output     : CNFRefutation 41.85s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 152 expanded)
%              Number of leaves         :   27 (  61 expanded)
%              Depth                    :   17
%              Number of atoms          :  118 ( 266 expanded)
%              Number of equality atoms :   28 (  57 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k10_relat_1(B,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t170_relat_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_34,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_26,plain,(
    ! [B_26,A_25] :
      ( k2_relat_1(k7_relat_1(B_26,A_25)) = k9_relat_1(B_26,A_25)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_23,B_24] :
      ( v1_relat_1(k7_relat_1(A_23,B_24))
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_30,C_32,B_31] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = k10_relat_1(k7_relat_1(C_32,A_30),B_31)
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_28,plain,(
    ! [A_27] :
      ( k10_relat_1(A_27,k2_relat_1(A_27)) = k1_relat_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_871,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(k10_relat_1(B_95,A_96),k10_relat_1(B_95,k2_relat_1(B_95)))
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6024,plain,(
    ! [A_182] :
      ( r1_tarski(k1_relat_1(A_182),k10_relat_1(A_182,k2_relat_1(A_182)))
      | ~ v1_relat_1(A_182)
      | ~ v1_relat_1(A_182) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_871])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_138,plain,(
    ! [A_45,B_46] :
      ( k2_xboole_0(A_45,B_46) = B_46
      | ~ r1_tarski(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    k2_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_138])).

tff(c_258,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(A_56,C_57)
      | ~ r1_tarski(k2_xboole_0(A_56,B_58),C_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_264,plain,(
    ! [C_57] :
      ( r1_tarski('#skF_1',C_57)
      | ~ r1_tarski(k1_relat_1('#skF_2'),C_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_258])).

tff(c_6041,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_6024,c_264])).

tff(c_6066,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6041])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k3_xboole_0(A_18,B_19) = A_18
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_6083,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1('#skF_2'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6066,c_20])).

tff(c_6192,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6083])).

tff(c_6227,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_6192])).

tff(c_4536,plain,(
    ! [A_160,A_161] :
      ( r1_tarski(k10_relat_1(A_160,A_161),k1_relat_1(A_160))
      | ~ v1_relat_1(A_160)
      | ~ v1_relat_1(A_160) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_871])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k2_xboole_0(A_11,B_12) = B_12
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21188,plain,(
    ! [A_358,A_359] :
      ( k2_xboole_0(k10_relat_1(A_358,A_359),k1_relat_1(A_358)) = k1_relat_1(A_358)
      | ~ v1_relat_1(A_358) ) ),
    inference(resolution,[status(thm)],[c_4536,c_14])).

tff(c_275,plain,(
    ! [A_56,B_58] : r1_tarski(A_56,k2_xboole_0(A_56,B_58)) ),
    inference(resolution,[status(thm)],[c_8,c_258])).

tff(c_21302,plain,(
    ! [A_360,A_361] :
      ( r1_tarski(k10_relat_1(A_360,A_361),k1_relat_1(A_360))
      | ~ v1_relat_1(A_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_21188,c_275])).

tff(c_21329,plain,
    ( r1_tarski('#skF_1',k1_relat_1(k7_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6227,c_21302])).

tff(c_106687,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_21329])).

tff(c_106690,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_106687])).

tff(c_106694,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_106690])).

tff(c_106696,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_21329])).

tff(c_92,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_92])).

tff(c_2141,plain,(
    ! [A_123,C_124,B_125] :
      ( k3_xboole_0(A_123,k10_relat_1(C_124,B_125)) = k10_relat_1(k7_relat_1(C_124,A_123),B_125)
      | ~ v1_relat_1(C_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_13565,plain,(
    ! [A_257,A_258] :
      ( k10_relat_1(k7_relat_1(A_257,A_258),k2_relat_1(A_257)) = k3_xboole_0(A_258,k1_relat_1(A_257))
      | ~ v1_relat_1(A_257)
      | ~ v1_relat_1(A_257) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_2141])).

tff(c_30,plain,(
    ! [B_29,A_28] :
      ( r1_tarski(k10_relat_1(B_29,A_28),k10_relat_1(B_29,k2_relat_1(B_29)))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_169505,plain,(
    ! [A_1236,A_1237] :
      ( r1_tarski(k3_xboole_0(A_1236,k1_relat_1(A_1237)),k10_relat_1(k7_relat_1(A_1237,A_1236),k2_relat_1(k7_relat_1(A_1237,A_1236))))
      | ~ v1_relat_1(k7_relat_1(A_1237,A_1236))
      | ~ v1_relat_1(A_1237)
      | ~ v1_relat_1(A_1237) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_13565,c_30])).

tff(c_169683,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_169505])).

tff(c_169743,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_106696,c_169683])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(k3_xboole_0(A_5,C_7),B_6)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_359,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_7353,plain,(
    ! [A_202,C_203,B_204] :
      ( k3_xboole_0(A_202,C_203) = B_204
      | ~ r1_tarski(B_204,k3_xboole_0(A_202,C_203))
      | ~ r1_tarski(A_202,B_204) ) ),
    inference(resolution,[status(thm)],[c_10,c_359])).

tff(c_7403,plain,(
    ! [A_30,C_32,B_31,B_204] :
      ( k3_xboole_0(A_30,k10_relat_1(C_32,B_31)) = B_204
      | ~ r1_tarski(B_204,k10_relat_1(k7_relat_1(C_32,A_30),B_31))
      | ~ r1_tarski(A_30,B_204)
      | ~ v1_relat_1(C_32) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_7353])).

tff(c_169757,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_169743,c_7403])).

tff(c_169817,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8,c_169757])).

tff(c_43,plain,(
    ! [B_38,A_39] : k3_xboole_0(B_38,A_39) = k3_xboole_0(A_39,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(k3_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_58,plain,(
    ! [B_38,A_39] : r1_tarski(k3_xboole_0(B_38,A_39),A_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_16])).

tff(c_170470,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(superposition,[status(thm),theory(equality)],[c_169817,c_58])).

tff(c_170690,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_170470])).

tff(c_170719,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_170690])).

tff(c_170721,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_170719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:05:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 41.85/31.78  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.85/31.79  
% 41.85/31.79  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.85/31.79  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 41.85/31.79  
% 41.85/31.79  %Foreground sorts:
% 41.85/31.79  
% 41.85/31.79  
% 41.85/31.79  %Background operators:
% 41.85/31.79  
% 41.85/31.79  
% 41.85/31.79  %Foreground operators:
% 41.85/31.79  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 41.85/31.79  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 41.85/31.79  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 41.85/31.79  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 41.85/31.79  tff('#skF_2', type, '#skF_2': $i).
% 41.85/31.79  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 41.85/31.79  tff('#skF_1', type, '#skF_1': $i).
% 41.85/31.79  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 41.85/31.79  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 41.85/31.79  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 41.85/31.79  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 41.85/31.79  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 41.85/31.79  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 41.85/31.79  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 41.85/31.79  
% 41.85/31.80  tff(f_90, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 41.85/31.80  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 41.85/31.80  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 41.85/31.80  tff(f_67, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 41.85/31.80  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 41.85/31.80  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 41.85/31.80  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k10_relat_1(B, k2_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t170_relat_1)).
% 41.85/31.80  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 41.85/31.80  tff(f_41, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 41.85/31.80  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 41.85/31.80  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 41.85/31.80  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 41.85/31.80  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 41.85/31.80  tff(c_34, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.85/31.80  tff(c_38, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.85/31.80  tff(c_26, plain, (![B_26, A_25]: (k2_relat_1(k7_relat_1(B_26, A_25))=k9_relat_1(B_26, A_25) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_71])).
% 41.85/31.80  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 41.85/31.80  tff(c_24, plain, (![A_23, B_24]: (v1_relat_1(k7_relat_1(A_23, B_24)) | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 41.85/31.80  tff(c_32, plain, (![A_30, C_32, B_31]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=k10_relat_1(k7_relat_1(C_32, A_30), B_31) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_83])).
% 41.85/31.80  tff(c_28, plain, (![A_27]: (k10_relat_1(A_27, k2_relat_1(A_27))=k1_relat_1(A_27) | ~v1_relat_1(A_27))), inference(cnfTransformation, [status(thm)], [f_75])).
% 41.85/31.80  tff(c_871, plain, (![B_95, A_96]: (r1_tarski(k10_relat_1(B_95, A_96), k10_relat_1(B_95, k2_relat_1(B_95))) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_79])).
% 41.85/31.80  tff(c_6024, plain, (![A_182]: (r1_tarski(k1_relat_1(A_182), k10_relat_1(A_182, k2_relat_1(A_182))) | ~v1_relat_1(A_182) | ~v1_relat_1(A_182))), inference(superposition, [status(thm), theory('equality')], [c_28, c_871])).
% 41.85/31.80  tff(c_36, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 41.85/31.80  tff(c_138, plain, (![A_45, B_46]: (k2_xboole_0(A_45, B_46)=B_46 | ~r1_tarski(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_45])).
% 41.85/31.80  tff(c_153, plain, (k2_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_36, c_138])).
% 41.85/31.80  tff(c_258, plain, (![A_56, C_57, B_58]: (r1_tarski(A_56, C_57) | ~r1_tarski(k2_xboole_0(A_56, B_58), C_57))), inference(cnfTransformation, [status(thm)], [f_41])).
% 41.85/31.80  tff(c_264, plain, (![C_57]: (r1_tarski('#skF_1', C_57) | ~r1_tarski(k1_relat_1('#skF_2'), C_57))), inference(superposition, [status(thm), theory('equality')], [c_153, c_258])).
% 41.85/31.80  tff(c_6041, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2'))) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_6024, c_264])).
% 41.85/31.80  tff(c_6066, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6041])).
% 41.85/31.80  tff(c_20, plain, (![A_18, B_19]: (k3_xboole_0(A_18, B_19)=A_18 | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_57])).
% 41.85/31.80  tff(c_6083, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1('#skF_2')))='#skF_1'), inference(resolution, [status(thm)], [c_6066, c_20])).
% 41.85/31.80  tff(c_6192, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_6083])).
% 41.85/31.80  tff(c_6227, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_6192])).
% 41.85/31.80  tff(c_4536, plain, (![A_160, A_161]: (r1_tarski(k10_relat_1(A_160, A_161), k1_relat_1(A_160)) | ~v1_relat_1(A_160) | ~v1_relat_1(A_160))), inference(superposition, [status(thm), theory('equality')], [c_28, c_871])).
% 41.85/31.80  tff(c_14, plain, (![A_11, B_12]: (k2_xboole_0(A_11, B_12)=B_12 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 41.85/31.80  tff(c_21188, plain, (![A_358, A_359]: (k2_xboole_0(k10_relat_1(A_358, A_359), k1_relat_1(A_358))=k1_relat_1(A_358) | ~v1_relat_1(A_358))), inference(resolution, [status(thm)], [c_4536, c_14])).
% 41.85/31.80  tff(c_275, plain, (![A_56, B_58]: (r1_tarski(A_56, k2_xboole_0(A_56, B_58)))), inference(resolution, [status(thm)], [c_8, c_258])).
% 41.85/31.80  tff(c_21302, plain, (![A_360, A_361]: (r1_tarski(k10_relat_1(A_360, A_361), k1_relat_1(A_360)) | ~v1_relat_1(A_360))), inference(superposition, [status(thm), theory('equality')], [c_21188, c_275])).
% 41.85/31.80  tff(c_21329, plain, (r1_tarski('#skF_1', k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_6227, c_21302])).
% 41.85/31.80  tff(c_106687, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_21329])).
% 41.85/31.80  tff(c_106690, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_106687])).
% 41.85/31.80  tff(c_106694, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_106690])).
% 41.85/31.80  tff(c_106696, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_21329])).
% 41.85/31.80  tff(c_92, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_57])).
% 41.85/31.80  tff(c_107, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_36, c_92])).
% 41.85/31.80  tff(c_2141, plain, (![A_123, C_124, B_125]: (k3_xboole_0(A_123, k10_relat_1(C_124, B_125))=k10_relat_1(k7_relat_1(C_124, A_123), B_125) | ~v1_relat_1(C_124))), inference(cnfTransformation, [status(thm)], [f_83])).
% 41.85/31.80  tff(c_13565, plain, (![A_257, A_258]: (k10_relat_1(k7_relat_1(A_257, A_258), k2_relat_1(A_257))=k3_xboole_0(A_258, k1_relat_1(A_257)) | ~v1_relat_1(A_257) | ~v1_relat_1(A_257))), inference(superposition, [status(thm), theory('equality')], [c_28, c_2141])).
% 41.85/31.80  tff(c_30, plain, (![B_29, A_28]: (r1_tarski(k10_relat_1(B_29, A_28), k10_relat_1(B_29, k2_relat_1(B_29))) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_79])).
% 41.85/31.80  tff(c_169505, plain, (![A_1236, A_1237]: (r1_tarski(k3_xboole_0(A_1236, k1_relat_1(A_1237)), k10_relat_1(k7_relat_1(A_1237, A_1236), k2_relat_1(k7_relat_1(A_1237, A_1236)))) | ~v1_relat_1(k7_relat_1(A_1237, A_1236)) | ~v1_relat_1(A_1237) | ~v1_relat_1(A_1237))), inference(superposition, [status(thm), theory('equality')], [c_13565, c_30])).
% 41.85/31.80  tff(c_169683, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_107, c_169505])).
% 41.85/31.80  tff(c_169743, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_106696, c_169683])).
% 41.85/31.80  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(k3_xboole_0(A_5, C_7), B_6) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 41.85/31.80  tff(c_359, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_33])).
% 41.85/31.80  tff(c_7353, plain, (![A_202, C_203, B_204]: (k3_xboole_0(A_202, C_203)=B_204 | ~r1_tarski(B_204, k3_xboole_0(A_202, C_203)) | ~r1_tarski(A_202, B_204))), inference(resolution, [status(thm)], [c_10, c_359])).
% 41.85/31.80  tff(c_7403, plain, (![A_30, C_32, B_31, B_204]: (k3_xboole_0(A_30, k10_relat_1(C_32, B_31))=B_204 | ~r1_tarski(B_204, k10_relat_1(k7_relat_1(C_32, A_30), B_31)) | ~r1_tarski(A_30, B_204) | ~v1_relat_1(C_32))), inference(superposition, [status(thm), theory('equality')], [c_32, c_7353])).
% 41.85/31.80  tff(c_169757, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_169743, c_7403])).
% 41.85/31.80  tff(c_169817, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8, c_169757])).
% 41.85/31.80  tff(c_43, plain, (![B_38, A_39]: (k3_xboole_0(B_38, A_39)=k3_xboole_0(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_27])).
% 41.85/31.80  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(k3_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 41.85/31.80  tff(c_58, plain, (![B_38, A_39]: (r1_tarski(k3_xboole_0(B_38, A_39), A_39))), inference(superposition, [status(thm), theory('equality')], [c_43, c_16])).
% 41.85/31.80  tff(c_170470, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(superposition, [status(thm), theory('equality')], [c_169817, c_58])).
% 41.85/31.80  tff(c_170690, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_26, c_170470])).
% 41.85/31.80  tff(c_170719, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_170690])).
% 41.85/31.80  tff(c_170721, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_170719])).
% 41.85/31.80  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 41.85/31.80  
% 41.85/31.80  Inference rules
% 41.85/31.80  ----------------------
% 41.85/31.80  #Ref     : 0
% 41.85/31.80  #Sup     : 43870
% 41.85/31.80  #Fact    : 0
% 41.85/31.80  #Define  : 0
% 41.85/31.80  #Split   : 2
% 41.85/31.80  #Chain   : 0
% 41.85/31.80  #Close   : 0
% 41.85/31.80  
% 41.85/31.80  Ordering : KBO
% 41.85/31.80  
% 41.85/31.80  Simplification rules
% 41.85/31.80  ----------------------
% 41.85/31.80  #Subsume      : 9325
% 41.85/31.80  #Demod        : 25988
% 41.85/31.80  #Tautology    : 16381
% 41.85/31.80  #SimpNegUnit  : 18
% 41.85/31.80  #BackRed      : 10
% 41.85/31.80  
% 41.85/31.80  #Partial instantiations: 0
% 41.85/31.80  #Strategies tried      : 1
% 41.85/31.80  
% 41.85/31.80  Timing (in seconds)
% 41.85/31.80  ----------------------
% 41.85/31.81  Preprocessing        : 0.31
% 41.85/31.81  Parsing              : 0.16
% 41.85/31.81  CNF conversion       : 0.02
% 41.85/31.81  Main loop            : 30.67
% 41.85/31.81  Inferencing          : 2.79
% 41.85/31.81  Reduction            : 16.13
% 41.85/31.81  Demodulation         : 14.74
% 41.85/31.81  BG Simplification    : 0.40
% 41.85/31.81  Subsumption          : 9.99
% 41.85/31.81  Abstraction          : 0.65
% 41.85/31.81  MUC search           : 0.00
% 41.85/31.81  Cooper               : 0.00
% 41.85/31.81  Total                : 31.02
% 41.85/31.81  Index Insertion      : 0.00
% 41.85/31.81  Index Deletion       : 0.00
% 41.85/31.81  Index Matching       : 0.00
% 41.85/31.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
