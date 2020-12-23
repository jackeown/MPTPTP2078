%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:42 EST 2020

% Result     : Theorem 5.70s
% Output     : CNFRefutation 5.70s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 312 expanded)
%              Number of leaves         :   25 ( 114 expanded)
%              Depth                    :   22
%              Number of atoms          :   97 ( 450 expanded)
%              Number of equality atoms :   40 ( 214 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r1_tarski(A,k1_relat_1(B))
         => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_35,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(c_20,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_24,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( k2_relat_1(k7_relat_1(B_12,A_11)) = k9_relat_1(B_12,A_11)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( v1_relat_1(k7_relat_1(A_9,B_10))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [A_27,B_28] :
      ( k3_xboole_0(A_27,B_28) = A_27
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_83,plain,(
    k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_75])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_60,plain,(
    ! [A_25,B_26] : k1_setfam_1(k2_tarski(A_25,B_26)) = k3_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_103,plain,(
    ! [B_29,A_30] : k1_setfam_1(k2_tarski(B_29,A_30)) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_60])).

tff(c_8,plain,(
    ! [A_7,B_8] : k1_setfam_1(k2_tarski(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_109,plain,(
    ! [B_29,A_30] : k3_xboole_0(B_29,A_30) = k3_xboole_0(A_30,B_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_36,B_37] : k3_xboole_0(k3_xboole_0(A_36,B_37),A_36) = k3_xboole_0(A_36,B_37) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_468,plain,(
    ! [A_48,B_49] : k3_xboole_0(k3_xboole_0(A_48,B_49),B_49) = k3_xboole_0(B_49,A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_109,c_197])).

tff(c_547,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = k3_xboole_0('#skF_1',k1_relat_1('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_468])).

tff(c_564,plain,(
    k3_xboole_0(k1_relat_1('#skF_2'),'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_547])).

tff(c_16,plain,(
    ! [B_15,A_14] :
      ( k3_xboole_0(k1_relat_1(B_15),A_14) = k1_relat_1(k7_relat_1(B_15,A_14))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_574,plain,
    ( k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_564,c_16])).

tff(c_616,plain,(
    k1_relat_1(k7_relat_1('#skF_2','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_574])).

tff(c_634,plain,(
    ! [A_14] :
      ( k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_14)) = k3_xboole_0('#skF_1',A_14)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_16])).

tff(c_831,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_634])).

tff(c_834,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_10,c_831])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_834])).

tff(c_840,plain,(
    v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_87,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_83,c_2])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_94,plain,(
    k3_xboole_0('#skF_1','#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_643,plain,(
    ! [A_50,C_51,B_52] :
      ( k3_xboole_0(A_50,k10_relat_1(C_51,B_52)) = k10_relat_1(k7_relat_1(C_51,A_50),B_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1855,plain,(
    ! [C_78,B_79,B_80] :
      ( k10_relat_1(k7_relat_1(C_78,k1_relat_1(B_79)),B_80) = k1_relat_1(k7_relat_1(B_79,k10_relat_1(C_78,B_80)))
      | ~ v1_relat_1(C_78)
      | ~ v1_relat_1(B_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_643])).

tff(c_14,plain,(
    ! [A_13] :
      ( k10_relat_1(A_13,k2_relat_1(A_13)) = k1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_709,plain,(
    ! [A_13,A_50] :
      ( k10_relat_1(k7_relat_1(A_13,A_50),k2_relat_1(A_13)) = k3_xboole_0(A_50,k1_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | ~ v1_relat_1(A_13) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_643])).

tff(c_4682,plain,(
    ! [B_129,C_130] :
      ( k1_relat_1(k7_relat_1(B_129,k10_relat_1(C_130,k2_relat_1(C_130)))) = k3_xboole_0(k1_relat_1(B_129),k1_relat_1(C_130))
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(B_129) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1855,c_709])).

tff(c_839,plain,(
    ! [A_14] : k1_relat_1(k7_relat_1(k7_relat_1('#skF_2','#skF_1'),A_14)) = k3_xboole_0('#skF_1',A_14) ),
    inference(splitRight,[status(thm)],[c_634])).

tff(c_4771,plain,(
    ! [C_130] :
      ( k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2','#skF_1')),k1_relat_1(C_130)) = k3_xboole_0('#skF_1',k10_relat_1(C_130,k2_relat_1(C_130)))
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(C_130)
      | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4682,c_839])).

tff(c_5021,plain,(
    ! [C_133] :
      ( k3_xboole_0('#skF_1',k10_relat_1(C_133,k2_relat_1(C_133))) = k3_xboole_0('#skF_1',k1_relat_1(C_133))
      | ~ v1_relat_1(C_133) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_616,c_4771])).

tff(c_126,plain,(
    ! [B_31,A_32] : k3_xboole_0(B_31,A_32) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_8])).

tff(c_141,plain,(
    ! [B_31,A_32] : r1_tarski(k3_xboole_0(B_31,A_32),A_32) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_2])).

tff(c_5149,plain,(
    ! [C_134] :
      ( r1_tarski(k3_xboole_0('#skF_1',k1_relat_1(C_134)),k10_relat_1(C_134,k2_relat_1(C_134)))
      | ~ v1_relat_1(C_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5021,c_141])).

tff(c_5187,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_1'),k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1'))))
    | ~ v1_relat_1(k7_relat_1('#skF_2','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_616,c_5149])).

tff(c_5202,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k2_relat_1(k7_relat_1('#skF_2','#skF_1')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_840,c_94,c_5187])).

tff(c_5809,plain,
    ( r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1')))
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_5202])).

tff(c_5815,plain,(
    r1_tarski('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5809])).

tff(c_5824,plain,(
    k3_xboole_0('#skF_1',k10_relat_1(k7_relat_1('#skF_2','#skF_1'),k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_5815,c_4])).

tff(c_82,plain,(
    ! [A_1,B_2] : k3_xboole_0(k3_xboole_0(A_1,B_2),A_1) = k3_xboole_0(A_1,B_2) ),
    inference(resolution,[status(thm)],[c_2,c_75])).

tff(c_675,plain,(
    ! [C_51,A_50,B_52] :
      ( k3_xboole_0(k10_relat_1(k7_relat_1(C_51,A_50),B_52),A_50) = k3_xboole_0(A_50,k10_relat_1(C_51,B_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_643,c_82])).

tff(c_720,plain,(
    ! [A_50,C_51,B_52] :
      ( k3_xboole_0(A_50,k10_relat_1(k7_relat_1(C_51,A_50),B_52)) = k3_xboole_0(A_50,k10_relat_1(C_51,B_52))
      | ~ v1_relat_1(C_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_675])).

tff(c_5830,plain,
    ( k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_5824,c_720])).

tff(c_5921,plain,(
    k3_xboole_0('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_5830])).

tff(c_6026,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_2',k9_relat_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_5921,c_141])).

tff(c_6058,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_6026])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n021.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:19 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.70/2.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.09  
% 5.70/2.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.09  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 5.70/2.09  
% 5.70/2.09  %Foreground sorts:
% 5.70/2.09  
% 5.70/2.09  
% 5.70/2.09  %Background operators:
% 5.70/2.09  
% 5.70/2.09  
% 5.70/2.09  %Foreground operators:
% 5.70/2.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.70/2.09  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.70/2.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.70/2.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.70/2.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.70/2.09  tff('#skF_2', type, '#skF_2': $i).
% 5.70/2.09  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 5.70/2.09  tff('#skF_1', type, '#skF_1': $i).
% 5.70/2.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.70/2.09  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 5.70/2.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.70/2.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.70/2.09  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.70/2.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.70/2.09  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 5.70/2.09  
% 5.70/2.11  tff(f_62, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t146_funct_1)).
% 5.70/2.11  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 5.70/2.11  tff(f_39, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 5.70/2.11  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.70/2.11  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 5.70/2.11  tff(f_35, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 5.70/2.11  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 5.70/2.11  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 5.70/2.11  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 5.70/2.11  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 5.70/2.11  tff(c_20, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.70/2.11  tff(c_24, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.70/2.11  tff(c_12, plain, (![B_12, A_11]: (k2_relat_1(k7_relat_1(B_12, A_11))=k9_relat_1(B_12, A_11) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.70/2.11  tff(c_10, plain, (![A_9, B_10]: (v1_relat_1(k7_relat_1(A_9, B_10)) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.70/2.11  tff(c_22, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.70/2.11  tff(c_75, plain, (![A_27, B_28]: (k3_xboole_0(A_27, B_28)=A_27 | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.11  tff(c_83, plain, (k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_22, c_75])).
% 5.70/2.11  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.70/2.11  tff(c_60, plain, (![A_25, B_26]: (k1_setfam_1(k2_tarski(A_25, B_26))=k3_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.11  tff(c_103, plain, (![B_29, A_30]: (k1_setfam_1(k2_tarski(B_29, A_30))=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_6, c_60])).
% 5.70/2.11  tff(c_8, plain, (![A_7, B_8]: (k1_setfam_1(k2_tarski(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.70/2.11  tff(c_109, plain, (![B_29, A_30]: (k3_xboole_0(B_29, A_30)=k3_xboole_0(A_30, B_29))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8])).
% 5.70/2.11  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.70/2.11  tff(c_197, plain, (![A_36, B_37]: (k3_xboole_0(k3_xboole_0(A_36, B_37), A_36)=k3_xboole_0(A_36, B_37))), inference(resolution, [status(thm)], [c_2, c_75])).
% 5.70/2.11  tff(c_468, plain, (![A_48, B_49]: (k3_xboole_0(k3_xboole_0(A_48, B_49), B_49)=k3_xboole_0(B_49, A_48))), inference(superposition, [status(thm), theory('equality')], [c_109, c_197])).
% 5.70/2.11  tff(c_547, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')=k3_xboole_0('#skF_1', k1_relat_1('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_83, c_468])).
% 5.70/2.11  tff(c_564, plain, (k3_xboole_0(k1_relat_1('#skF_2'), '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_83, c_547])).
% 5.70/2.11  tff(c_16, plain, (![B_15, A_14]: (k3_xboole_0(k1_relat_1(B_15), A_14)=k1_relat_1(k7_relat_1(B_15, A_14)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.70/2.11  tff(c_574, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_564, c_16])).
% 5.70/2.11  tff(c_616, plain, (k1_relat_1(k7_relat_1('#skF_2', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_574])).
% 5.70/2.11  tff(c_634, plain, (![A_14]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_14))=k3_xboole_0('#skF_1', A_14) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_616, c_16])).
% 5.70/2.11  tff(c_831, plain, (~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitLeft, [status(thm)], [c_634])).
% 5.70/2.11  tff(c_834, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_10, c_831])).
% 5.70/2.11  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_834])).
% 5.70/2.11  tff(c_840, plain, (v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(splitRight, [status(thm)], [c_634])).
% 5.70/2.11  tff(c_87, plain, (r1_tarski('#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_83, c_2])).
% 5.70/2.11  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.70/2.11  tff(c_94, plain, (k3_xboole_0('#skF_1', '#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_87, c_4])).
% 5.70/2.11  tff(c_643, plain, (![A_50, C_51, B_52]: (k3_xboole_0(A_50, k10_relat_1(C_51, B_52))=k10_relat_1(k7_relat_1(C_51, A_50), B_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.70/2.11  tff(c_1855, plain, (![C_78, B_79, B_80]: (k10_relat_1(k7_relat_1(C_78, k1_relat_1(B_79)), B_80)=k1_relat_1(k7_relat_1(B_79, k10_relat_1(C_78, B_80))) | ~v1_relat_1(C_78) | ~v1_relat_1(B_79))), inference(superposition, [status(thm), theory('equality')], [c_16, c_643])).
% 5.70/2.11  tff(c_14, plain, (![A_13]: (k10_relat_1(A_13, k2_relat_1(A_13))=k1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.70/2.11  tff(c_709, plain, (![A_13, A_50]: (k10_relat_1(k7_relat_1(A_13, A_50), k2_relat_1(A_13))=k3_xboole_0(A_50, k1_relat_1(A_13)) | ~v1_relat_1(A_13) | ~v1_relat_1(A_13))), inference(superposition, [status(thm), theory('equality')], [c_14, c_643])).
% 5.70/2.11  tff(c_4682, plain, (![B_129, C_130]: (k1_relat_1(k7_relat_1(B_129, k10_relat_1(C_130, k2_relat_1(C_130))))=k3_xboole_0(k1_relat_1(B_129), k1_relat_1(C_130)) | ~v1_relat_1(C_130) | ~v1_relat_1(C_130) | ~v1_relat_1(C_130) | ~v1_relat_1(B_129))), inference(superposition, [status(thm), theory('equality')], [c_1855, c_709])).
% 5.70/2.11  tff(c_839, plain, (![A_14]: (k1_relat_1(k7_relat_1(k7_relat_1('#skF_2', '#skF_1'), A_14))=k3_xboole_0('#skF_1', A_14))), inference(splitRight, [status(thm)], [c_634])).
% 5.70/2.11  tff(c_4771, plain, (![C_130]: (k3_xboole_0(k1_relat_1(k7_relat_1('#skF_2', '#skF_1')), k1_relat_1(C_130))=k3_xboole_0('#skF_1', k10_relat_1(C_130, k2_relat_1(C_130))) | ~v1_relat_1(C_130) | ~v1_relat_1(C_130) | ~v1_relat_1(C_130) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_4682, c_839])).
% 5.70/2.11  tff(c_5021, plain, (![C_133]: (k3_xboole_0('#skF_1', k10_relat_1(C_133, k2_relat_1(C_133)))=k3_xboole_0('#skF_1', k1_relat_1(C_133)) | ~v1_relat_1(C_133))), inference(demodulation, [status(thm), theory('equality')], [c_840, c_616, c_4771])).
% 5.70/2.11  tff(c_126, plain, (![B_31, A_32]: (k3_xboole_0(B_31, A_32)=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_103, c_8])).
% 5.70/2.11  tff(c_141, plain, (![B_31, A_32]: (r1_tarski(k3_xboole_0(B_31, A_32), A_32))), inference(superposition, [status(thm), theory('equality')], [c_126, c_2])).
% 5.70/2.11  tff(c_5149, plain, (![C_134]: (r1_tarski(k3_xboole_0('#skF_1', k1_relat_1(C_134)), k10_relat_1(C_134, k2_relat_1(C_134))) | ~v1_relat_1(C_134))), inference(superposition, [status(thm), theory('equality')], [c_5021, c_141])).
% 5.70/2.11  tff(c_5187, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_1'), k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1')))) | ~v1_relat_1(k7_relat_1('#skF_2', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_616, c_5149])).
% 5.70/2.11  tff(c_5202, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k2_relat_1(k7_relat_1('#skF_2', '#skF_1'))))), inference(demodulation, [status(thm), theory('equality')], [c_840, c_94, c_5187])).
% 5.70/2.11  tff(c_5809, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1'))) | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_12, c_5202])).
% 5.70/2.11  tff(c_5815, plain, (r1_tarski('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5809])).
% 5.70/2.11  tff(c_5824, plain, (k3_xboole_0('#skF_1', k10_relat_1(k7_relat_1('#skF_2', '#skF_1'), k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(resolution, [status(thm)], [c_5815, c_4])).
% 5.70/2.11  tff(c_82, plain, (![A_1, B_2]: (k3_xboole_0(k3_xboole_0(A_1, B_2), A_1)=k3_xboole_0(A_1, B_2))), inference(resolution, [status(thm)], [c_2, c_75])).
% 5.70/2.11  tff(c_675, plain, (![C_51, A_50, B_52]: (k3_xboole_0(k10_relat_1(k7_relat_1(C_51, A_50), B_52), A_50)=k3_xboole_0(A_50, k10_relat_1(C_51, B_52)) | ~v1_relat_1(C_51))), inference(superposition, [status(thm), theory('equality')], [c_643, c_82])).
% 5.70/2.11  tff(c_720, plain, (![A_50, C_51, B_52]: (k3_xboole_0(A_50, k10_relat_1(k7_relat_1(C_51, A_50), B_52))=k3_xboole_0(A_50, k10_relat_1(C_51, B_52)) | ~v1_relat_1(C_51))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_675])).
% 5.70/2.11  tff(c_5830, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_5824, c_720])).
% 5.70/2.11  tff(c_5921, plain, (k3_xboole_0('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_5830])).
% 5.70/2.11  tff(c_6026, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_2', k9_relat_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_5921, c_141])).
% 5.70/2.11  tff(c_6058, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_6026])).
% 5.70/2.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.70/2.11  
% 5.70/2.11  Inference rules
% 5.70/2.11  ----------------------
% 5.70/2.11  #Ref     : 0
% 5.70/2.11  #Sup     : 1517
% 5.70/2.11  #Fact    : 0
% 5.70/2.11  #Define  : 0
% 5.70/2.11  #Split   : 4
% 5.70/2.11  #Chain   : 0
% 5.70/2.11  #Close   : 0
% 5.70/2.11  
% 5.70/2.11  Ordering : KBO
% 5.70/2.11  
% 5.70/2.11  Simplification rules
% 5.70/2.11  ----------------------
% 5.70/2.11  #Subsume      : 184
% 5.70/2.11  #Demod        : 1566
% 5.70/2.11  #Tautology    : 770
% 5.70/2.11  #SimpNegUnit  : 1
% 5.70/2.11  #BackRed      : 1
% 5.70/2.11  
% 5.70/2.11  #Partial instantiations: 0
% 5.70/2.11  #Strategies tried      : 1
% 5.70/2.11  
% 5.70/2.11  Timing (in seconds)
% 5.70/2.11  ----------------------
% 5.86/2.11  Preprocessing        : 0.28
% 5.86/2.11  Parsing              : 0.14
% 5.86/2.11  CNF conversion       : 0.02
% 5.86/2.11  Main loop            : 1.06
% 5.86/2.11  Inferencing          : 0.32
% 5.86/2.11  Reduction            : 0.48
% 5.86/2.11  Demodulation         : 0.40
% 5.86/2.11  BG Simplification    : 0.04
% 5.86/2.11  Subsumption          : 0.16
% 5.86/2.11  Abstraction          : 0.06
% 5.86/2.11  MUC search           : 0.00
% 5.86/2.11  Cooper               : 0.00
% 5.86/2.11  Total                : 1.37
% 5.86/2.11  Index Insertion      : 0.00
% 5.86/2.11  Index Deletion       : 0.00
% 5.86/2.11  Index Matching       : 0.00
% 5.86/2.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
