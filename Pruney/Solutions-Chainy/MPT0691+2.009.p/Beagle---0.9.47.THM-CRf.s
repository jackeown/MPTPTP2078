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
% DateTime   : Thu Dec  3 10:04:40 EST 2020

% Result     : Theorem 3.82s
% Output     : CNFRefutation 3.82s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 298 expanded)
%              Number of leaves         :   33 ( 112 expanded)
%              Depth                    :   17
%              Number of atoms          :   96 ( 409 expanded)
%              Number of equality atoms :   52 ( 230 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_47,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( r1_tarski(B,C)
         => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_140,plain,(
    ! [A_42,B_43] :
      ( r1_tarski(A_42,B_43)
      | k4_xboole_0(A_42,B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_36,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_148,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_140,c_36])).

tff(c_40,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_110,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(A_39,B_40) = k1_xboole_0
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_118,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_110])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_314,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_338,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_314])).

tff(c_343,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_338])).

tff(c_24,plain,(
    ! [A_16,B_17] :
      ( v1_relat_1(k7_relat_1(A_16,B_17))
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_494,plain,(
    ! [B_63,A_64] :
      ( k3_xboole_0(k1_relat_1(B_63),A_64) = k1_relat_1(k7_relat_1(B_63,A_64))
      | ~ v1_relat_1(B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_20,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_95,plain,(
    ! [A_37,B_38] : k1_setfam_1(k2_tarski(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_149,plain,(
    ! [A_44,B_45] : k1_setfam_1(k2_tarski(A_44,B_45)) = k3_xboole_0(B_45,A_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_95])).

tff(c_22,plain,(
    ! [A_14,B_15] : k1_setfam_1(k2_tarski(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_155,plain,(
    ! [B_45,A_44] : k3_xboole_0(B_45,A_44) = k3_xboole_0(A_44,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_149,c_22])).

tff(c_762,plain,(
    ! [A_81,B_82] :
      ( k3_xboole_0(A_81,k1_relat_1(B_82)) = k1_relat_1(k7_relat_1(B_82,A_81))
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_155])).

tff(c_16,plain,(
    ! [A_9] : k4_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_117,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_110])).

tff(c_205,plain,(
    ! [A_48,B_49] : k4_xboole_0(A_48,k4_xboole_0(A_48,B_49)) = k3_xboole_0(A_48,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = k4_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_205])).

tff(c_229,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_220])).

tff(c_781,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_762,c_229])).

tff(c_830,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_781])).

tff(c_517,plain,(
    ! [B_63] :
      ( k1_relat_1(k7_relat_1(B_63,k1_relat_1(B_63))) = k1_relat_1(B_63)
      | ~ v1_relat_1(B_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_494,c_2])).

tff(c_841,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_517])).

tff(c_850,plain,
    ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1')) = '#skF_1'
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_841])).

tff(c_1008,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_1012,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_1008])).

tff(c_1016,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1012])).

tff(c_1018,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_26,plain,(
    ! [A_18] :
      ( k9_relat_1(A_18,k1_relat_1(A_18)) = k2_relat_1(A_18)
      | ~ v1_relat_1(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_847,plain,
    ( k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_26])).

tff(c_1674,plain,(
    k9_relat_1(k7_relat_1('#skF_2','#skF_1'),'#skF_1') = k2_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_847])).

tff(c_28,plain,(
    ! [A_19,C_23,B_22] :
      ( k9_relat_1(k7_relat_1(A_19,C_23),B_22) = k9_relat_1(A_19,B_22)
      | ~ r1_tarski(B_22,C_23)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1678,plain,
    ( k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1')
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1674,c_28])).

tff(c_1685,plain,(
    k2_relat_1(k7_relat_1('#skF_2','#skF_1')) = k9_relat_1('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_8,c_1678])).

tff(c_30,plain,(
    ! [A_24] :
      ( k10_relat_1(A_24,k2_relat_1(A_24)) = k1_relat_1(A_24)
      | ~ v1_relat_1(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1693,plain,
    ( k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = k1_relat_1(k7_relat_1('#skF_2','#skF_1'))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1685,c_30])).

tff(c_1697,plain,(
    k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_830,c_1693])).

tff(c_595,plain,(
    ! [A_69,C_70,B_71] :
      ( k3_xboole_0(A_69,k10_relat_1(C_70,B_71)) = k10_relat_1(k7_relat_1(C_70,A_69),B_71)
      | ~ v1_relat_1(C_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_608,plain,(
    ! [A_69,C_70,B_71] :
      ( k5_xboole_0(A_69,k10_relat_1(k7_relat_1(C_70,A_69),B_71)) = k4_xboole_0(A_69,k10_relat_1(C_70,B_71))
      | ~ v1_relat_1(C_70) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_595,c_14])).

tff(c_1719,plain,
    ( k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k5_xboole_0('#skF_1','#skF_1')
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1697,c_608])).

tff(c_1732,plain,(
    k4_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_343,c_1719])).

tff(c_1734,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_148,c_1732])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:28:37 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.82/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.70  
% 3.82/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.70  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 3.82/1.70  
% 3.82/1.70  %Foreground sorts:
% 3.82/1.70  
% 3.82/1.70  
% 3.82/1.70  %Background operators:
% 3.82/1.70  
% 3.82/1.70  
% 3.82/1.70  %Foreground operators:
% 3.82/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.82/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.82/1.70  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.82/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.82/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.82/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.82/1.70  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.82/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.82/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.82/1.70  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.82/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.82/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.82/1.70  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.82/1.70  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.82/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.82/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.82/1.70  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.82/1.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.82/1.70  
% 3.82/1.72  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.82/1.72  tff(f_81, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.82/1.72  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.82/1.72  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.82/1.72  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.82/1.72  tff(f_51, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 3.82/1.72  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t90_relat_1)).
% 3.82/1.72  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.82/1.72  tff(f_47, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.82/1.72  tff(f_41, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.82/1.72  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.82/1.72  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 3.82/1.72  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t162_relat_1)).
% 3.82/1.72  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t169_relat_1)).
% 3.82/1.72  tff(f_74, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_funct_1)).
% 3.82/1.72  tff(c_140, plain, (![A_42, B_43]: (r1_tarski(A_42, B_43) | k4_xboole_0(A_42, B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.72  tff(c_36, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.82/1.72  tff(c_148, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))!=k1_xboole_0), inference(resolution, [status(thm)], [c_140, c_36])).
% 3.82/1.72  tff(c_40, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.82/1.72  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.82/1.72  tff(c_110, plain, (![A_39, B_40]: (k4_xboole_0(A_39, B_40)=k1_xboole_0 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.82/1.72  tff(c_118, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_110])).
% 3.82/1.72  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.82/1.72  tff(c_314, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.72  tff(c_338, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_314])).
% 3.82/1.72  tff(c_343, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_118, c_338])).
% 3.82/1.72  tff(c_24, plain, (![A_16, B_17]: (v1_relat_1(k7_relat_1(A_16, B_17)) | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.82/1.72  tff(c_494, plain, (![B_63, A_64]: (k3_xboole_0(k1_relat_1(B_63), A_64)=k1_relat_1(k7_relat_1(B_63, A_64)) | ~v1_relat_1(B_63))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.82/1.72  tff(c_20, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.82/1.72  tff(c_95, plain, (![A_37, B_38]: (k1_setfam_1(k2_tarski(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.72  tff(c_149, plain, (![A_44, B_45]: (k1_setfam_1(k2_tarski(A_44, B_45))=k3_xboole_0(B_45, A_44))), inference(superposition, [status(thm), theory('equality')], [c_20, c_95])).
% 3.82/1.72  tff(c_22, plain, (![A_14, B_15]: (k1_setfam_1(k2_tarski(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.82/1.72  tff(c_155, plain, (![B_45, A_44]: (k3_xboole_0(B_45, A_44)=k3_xboole_0(A_44, B_45))), inference(superposition, [status(thm), theory('equality')], [c_149, c_22])).
% 3.82/1.72  tff(c_762, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k1_relat_1(B_82))=k1_relat_1(k7_relat_1(B_82, A_81)) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_494, c_155])).
% 3.82/1.72  tff(c_16, plain, (![A_9]: (k4_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.82/1.72  tff(c_38, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.82/1.72  tff(c_117, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_110])).
% 3.82/1.72  tff(c_205, plain, (![A_48, B_49]: (k4_xboole_0(A_48, k4_xboole_0(A_48, B_49))=k3_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.82/1.72  tff(c_220, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))=k4_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_117, c_205])).
% 3.82/1.72  tff(c_229, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_220])).
% 3.82/1.72  tff(c_781, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_762, c_229])).
% 3.82/1.72  tff(c_830, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_781])).
% 3.82/1.72  tff(c_517, plain, (![B_63]: (k1_relat_1(k7_relat_1(B_63, k1_relat_1(B_63)))=k1_relat_1(B_63) | ~v1_relat_1(B_63))), inference(superposition, [status(thm), theory('equality')], [c_494, c_2])).
% 3.82/1.72  tff(c_841, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_830, c_517])).
% 3.82/1.72  tff(c_850, plain, (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1'))='#skF_1' | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_830, c_841])).
% 3.82/1.72  tff(c_1008, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_850])).
% 3.82/1.72  tff(c_1012, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_24, c_1008])).
% 3.82/1.72  tff(c_1016, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_1012])).
% 3.82/1.72  tff(c_1018, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_850])).
% 3.82/1.72  tff(c_26, plain, (![A_18]: (k9_relat_1(A_18, k1_relat_1(A_18))=k2_relat_1(A_18) | ~v1_relat_1(A_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.82/1.72  tff(c_847, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_830, c_26])).
% 3.82/1.72  tff(c_1674, plain, (k9_relat_1(k7_relat_1('#skF_2', '#skF_1'), '#skF_1')=k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_847])).
% 3.82/1.72  tff(c_28, plain, (![A_19, C_23, B_22]: (k9_relat_1(k7_relat_1(A_19, C_23), B_22)=k9_relat_1(A_19, B_22) | ~r1_tarski(B_22, C_23) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.82/1.72  tff(c_1678, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1') | ~r1_tarski('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1674, c_28])).
% 3.82/1.72  tff(c_1685, plain, (k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))=k9_relat_1('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_8, c_1678])).
% 3.82/1.72  tff(c_30, plain, (![A_24]: (k10_relat_1(A_24, k2_relat_1(A_24))=k1_relat_1(A_24) | ~v1_relat_1(A_24))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.82/1.72  tff(c_1693, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))=k1_relat_1(k7_relat_1('#skF_2', '#skF_1')) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1685, c_30])).
% 3.82/1.72  tff(c_1697, plain, (k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_830, c_1693])).
% 3.82/1.72  tff(c_595, plain, (![A_69, C_70, B_71]: (k3_xboole_0(A_69, k10_relat_1(C_70, B_71))=k10_relat_1(k7_relat_1(C_70, A_69), B_71) | ~v1_relat_1(C_70))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.82/1.72  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.82/1.72  tff(c_608, plain, (![A_69, C_70, B_71]: (k5_xboole_0(A_69, k10_relat_1(k7_relat_1(C_70, A_69), B_71))=k4_xboole_0(A_69, k10_relat_1(C_70, B_71)) | ~v1_relat_1(C_70))), inference(superposition, [status(thm), theory('equality')], [c_595, c_14])).
% 3.82/1.72  tff(c_1719, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k5_xboole_0('#skF_1', '#skF_1') | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1697, c_608])).
% 3.82/1.72  tff(c_1732, plain, (k4_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_40, c_343, c_1719])).
% 3.82/1.72  tff(c_1734, plain, $false, inference(negUnitSimplification, [status(thm)], [c_148, c_1732])).
% 3.82/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.82/1.72  
% 3.82/1.72  Inference rules
% 3.82/1.72  ----------------------
% 3.82/1.72  #Ref     : 0
% 3.82/1.72  #Sup     : 431
% 3.82/1.72  #Fact    : 0
% 3.82/1.72  #Define  : 0
% 3.82/1.72  #Split   : 3
% 3.82/1.72  #Chain   : 0
% 3.82/1.72  #Close   : 0
% 3.82/1.72  
% 3.82/1.72  Ordering : KBO
% 3.82/1.72  
% 3.82/1.72  Simplification rules
% 3.82/1.72  ----------------------
% 3.82/1.72  #Subsume      : 34
% 3.82/1.72  #Demod        : 274
% 3.82/1.72  #Tautology    : 241
% 3.82/1.72  #SimpNegUnit  : 1
% 3.82/1.72  #BackRed      : 2
% 3.82/1.72  
% 3.82/1.72  #Partial instantiations: 0
% 3.82/1.72  #Strategies tried      : 1
% 3.82/1.72  
% 3.82/1.72  Timing (in seconds)
% 3.82/1.72  ----------------------
% 3.82/1.72  Preprocessing        : 0.34
% 3.82/1.72  Parsing              : 0.18
% 3.82/1.72  CNF conversion       : 0.02
% 3.82/1.72  Main loop            : 0.56
% 3.82/1.72  Inferencing          : 0.20
% 3.82/1.72  Reduction            : 0.21
% 3.82/1.73  Demodulation         : 0.17
% 3.82/1.73  BG Simplification    : 0.03
% 3.82/1.73  Subsumption          : 0.09
% 3.82/1.73  Abstraction          : 0.03
% 3.82/1.73  MUC search           : 0.00
% 4.00/1.73  Cooper               : 0.00
% 4.00/1.73  Total                : 0.93
% 4.00/1.73  Index Insertion      : 0.00
% 4.00/1.73  Index Deletion       : 0.00
% 4.00/1.73  Index Matching       : 0.00
% 4.00/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
