%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:42 EST 2020

% Result     : Theorem 10.40s
% Output     : CNFRefutation 10.40s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 135 expanded)
%              Number of leaves         :   38 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :  101 ( 180 expanded)
%              Number of equality atoms :   51 (  97 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_tarski(A,B)
         => k2_wellord1(k2_wellord1(C,B),A) = k2_wellord1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_wellord1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(k2_wellord1(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_wellord1)).

tff(c_14,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_48,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_50,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_8,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_123,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k4_xboole_0(A_54,B_55)) = k3_xboole_0(A_54,B_55) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_141,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k3_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_123])).

tff(c_144,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_141])).

tff(c_24,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [C_25,A_23,B_24] :
      ( k6_subset_1(k7_relat_1(C_25,A_23),k7_relat_1(C_25,B_24)) = k7_relat_1(C_25,k6_subset_1(A_23,B_24))
      | ~ v1_relat_1(C_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_768,plain,(
    ! [C_96,A_97,B_98] :
      ( k4_xboole_0(k7_relat_1(C_96,A_97),k7_relat_1(C_96,B_98)) = k7_relat_1(C_96,k4_xboole_0(A_97,B_98))
      | ~ v1_relat_1(C_96) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_24,c_28])).

tff(c_778,plain,(
    ! [C_96,B_98] :
      ( k7_relat_1(C_96,k4_xboole_0(B_98,B_98)) = k1_xboole_0
      | ~ v1_relat_1(C_96) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_768,c_144])).

tff(c_822,plain,(
    ! [C_99] :
      ( k7_relat_1(C_99,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_99) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_778])).

tff(c_830,plain,(
    k7_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_50,c_822])).

tff(c_10,plain,(
    ! [A_4] : r1_tarski(k1_xboole_0,A_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_481,plain,(
    ! [B_80,A_81] :
      ( k1_relat_1(k7_relat_1(B_80,A_81)) = A_81
      | ~ r1_tarski(A_81,k1_relat_1(B_80))
      | ~ v1_relat_1(B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_506,plain,(
    ! [B_80] :
      ( k1_relat_1(k7_relat_1(B_80,k1_xboole_0)) = k1_xboole_0
      | ~ v1_relat_1(B_80) ) ),
    inference(resolution,[status(thm)],[c_10,c_481])).

tff(c_840,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_506])).

tff(c_848,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_840])).

tff(c_38,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_30,plain,(
    ! [A_26] : k1_relat_1(k6_relat_1(A_26)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_368,plain,(
    ! [B_72,A_73] :
      ( k7_relat_1(B_72,A_73) = B_72
      | ~ r1_tarski(k1_relat_1(B_72),A_73)
      | ~ v1_relat_1(B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_371,plain,(
    ! [A_26,A_73] :
      ( k7_relat_1(k6_relat_1(A_26),A_73) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_73)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_368])).

tff(c_377,plain,(
    ! [A_26,A_73] :
      ( k7_relat_1(k6_relat_1(A_26),A_73) = k6_relat_1(A_26)
      | ~ r1_tarski(A_26,A_73) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_371])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_378,plain,(
    ! [B_72] :
      ( k7_relat_1(B_72,k1_relat_1(B_72)) = B_72
      | ~ v1_relat_1(B_72) ) ),
    inference(resolution,[status(thm)],[c_6,c_368])).

tff(c_27163,plain,(
    ! [B_411,B_412] :
      ( k7_relat_1(B_411,k4_xboole_0(k1_relat_1(B_411),B_412)) = k4_xboole_0(B_411,k7_relat_1(B_411,B_412))
      | ~ v1_relat_1(B_411)
      | ~ v1_relat_1(B_411) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_378,c_768])).

tff(c_492,plain,(
    ! [A_26,A_81] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_26),A_81)) = A_81
      | ~ r1_tarski(A_81,A_26)
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_481])).

tff(c_504,plain,(
    ! [A_26,A_81] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_26),A_81)) = A_81
      | ~ r1_tarski(A_81,A_26) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_492])).

tff(c_27247,plain,(
    ! [A_26,B_412] :
      ( k1_relat_1(k4_xboole_0(k6_relat_1(A_26),k7_relat_1(k6_relat_1(A_26),B_412))) = k4_xboole_0(k1_relat_1(k6_relat_1(A_26)),B_412)
      | ~ r1_tarski(k4_xboole_0(k1_relat_1(k6_relat_1(A_26)),B_412),A_26)
      | ~ v1_relat_1(k6_relat_1(A_26))
      | ~ v1_relat_1(k6_relat_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_27163,c_504])).

tff(c_30033,plain,(
    ! [A_424,B_425] : k1_relat_1(k4_xboole_0(k6_relat_1(A_424),k7_relat_1(k6_relat_1(A_424),B_425))) = k4_xboole_0(A_424,B_425) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_12,c_30,c_30,c_27247])).

tff(c_30294,plain,(
    ! [A_26,A_73] :
      ( k4_xboole_0(A_26,A_73) = k1_relat_1(k4_xboole_0(k6_relat_1(A_26),k6_relat_1(A_26)))
      | ~ r1_tarski(A_26,A_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_30033])).

tff(c_30382,plain,(
    ! [A_426,A_427] :
      ( k4_xboole_0(A_426,A_427) = k1_xboole_0
      | ~ r1_tarski(A_426,A_427) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_144,c_30294])).

tff(c_30551,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_30382])).

tff(c_16,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30593,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_30551,c_16])).

tff(c_30609,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30593])).

tff(c_719,plain,(
    ! [C_93,A_94,B_95] :
      ( k2_wellord1(k2_wellord1(C_93,A_94),B_95) = k2_wellord1(C_93,k3_xboole_0(A_94,B_95))
      | ~ v1_relat_1(C_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_652,plain,(
    ! [C_90,B_91,A_92] :
      ( k2_wellord1(k2_wellord1(C_90,B_91),A_92) = k2_wellord1(k2_wellord1(C_90,A_92),B_91)
      | ~ v1_relat_1(C_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_46,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_2'),'#skF_1') != k2_wellord1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_679,plain,
    ( k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_652,c_46])).

tff(c_712,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_679])).

tff(c_728,plain,
    ( k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_719,c_712])).

tff(c_764,plain,(
    k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) != k2_wellord1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_728])).

tff(c_30746,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30609,c_764])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:47:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.40/4.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/4.27  
% 10.40/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/4.28  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.40/4.28  
% 10.40/4.28  %Foreground sorts:
% 10.40/4.28  
% 10.40/4.28  
% 10.40/4.28  %Background operators:
% 10.40/4.28  
% 10.40/4.28  
% 10.40/4.28  %Foreground operators:
% 10.40/4.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.40/4.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.40/4.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.40/4.28  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.40/4.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.40/4.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.40/4.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.40/4.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.40/4.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.40/4.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.40/4.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.40/4.28  tff('#skF_2', type, '#skF_2': $i).
% 10.40/4.28  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 10.40/4.28  tff('#skF_3', type, '#skF_3': $i).
% 10.40/4.28  tff('#skF_1', type, '#skF_1': $i).
% 10.40/4.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.40/4.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.40/4.28  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.40/4.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.40/4.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.40/4.28  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 10.40/4.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.40/4.28  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.40/4.28  
% 10.40/4.29  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 10.40/4.29  tff(f_90, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k2_wellord1(k2_wellord1(C, B), A) = k2_wellord1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_wellord1)).
% 10.40/4.29  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 10.40/4.29  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.40/4.29  tff(f_49, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 10.40/4.29  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 10.40/4.29  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 10.40/4.29  tff(f_65, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 10.40/4.29  tff(f_75, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.40/4.29  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 10.40/4.29  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 10.40/4.29  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 10.40/4.29  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.40/4.29  tff(f_79, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t26_wellord1)).
% 10.40/4.29  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(k2_wellord1(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t27_wellord1)).
% 10.40/4.29  tff(c_14, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.40/4.29  tff(c_48, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.40/4.29  tff(c_50, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.40/4.29  tff(c_8, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.40/4.29  tff(c_123, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k4_xboole_0(A_54, B_55))=k3_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.40/4.29  tff(c_141, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k3_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_123])).
% 10.40/4.29  tff(c_144, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_141])).
% 10.40/4.29  tff(c_24, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.40/4.29  tff(c_28, plain, (![C_25, A_23, B_24]: (k6_subset_1(k7_relat_1(C_25, A_23), k7_relat_1(C_25, B_24))=k7_relat_1(C_25, k6_subset_1(A_23, B_24)) | ~v1_relat_1(C_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 10.40/4.29  tff(c_768, plain, (![C_96, A_97, B_98]: (k4_xboole_0(k7_relat_1(C_96, A_97), k7_relat_1(C_96, B_98))=k7_relat_1(C_96, k4_xboole_0(A_97, B_98)) | ~v1_relat_1(C_96))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_24, c_28])).
% 10.40/4.29  tff(c_778, plain, (![C_96, B_98]: (k7_relat_1(C_96, k4_xboole_0(B_98, B_98))=k1_xboole_0 | ~v1_relat_1(C_96))), inference(superposition, [status(thm), theory('equality')], [c_768, c_144])).
% 10.40/4.29  tff(c_822, plain, (![C_99]: (k7_relat_1(C_99, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_99))), inference(demodulation, [status(thm), theory('equality')], [c_144, c_778])).
% 10.40/4.29  tff(c_830, plain, (k7_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_50, c_822])).
% 10.40/4.29  tff(c_10, plain, (![A_4]: (r1_tarski(k1_xboole_0, A_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.40/4.29  tff(c_481, plain, (![B_80, A_81]: (k1_relat_1(k7_relat_1(B_80, A_81))=A_81 | ~r1_tarski(A_81, k1_relat_1(B_80)) | ~v1_relat_1(B_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.40/4.29  tff(c_506, plain, (![B_80]: (k1_relat_1(k7_relat_1(B_80, k1_xboole_0))=k1_xboole_0 | ~v1_relat_1(B_80))), inference(resolution, [status(thm)], [c_10, c_481])).
% 10.40/4.29  tff(c_840, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_830, c_506])).
% 10.40/4.29  tff(c_848, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_50, c_840])).
% 10.40/4.29  tff(c_38, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 10.40/4.29  tff(c_30, plain, (![A_26]: (k1_relat_1(k6_relat_1(A_26))=A_26)), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.40/4.29  tff(c_368, plain, (![B_72, A_73]: (k7_relat_1(B_72, A_73)=B_72 | ~r1_tarski(k1_relat_1(B_72), A_73) | ~v1_relat_1(B_72))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.40/4.29  tff(c_371, plain, (![A_26, A_73]: (k7_relat_1(k6_relat_1(A_26), A_73)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_73) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_368])).
% 10.40/4.29  tff(c_377, plain, (![A_26, A_73]: (k7_relat_1(k6_relat_1(A_26), A_73)=k6_relat_1(A_26) | ~r1_tarski(A_26, A_73))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_371])).
% 10.40/4.29  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.40/4.29  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.40/4.29  tff(c_378, plain, (![B_72]: (k7_relat_1(B_72, k1_relat_1(B_72))=B_72 | ~v1_relat_1(B_72))), inference(resolution, [status(thm)], [c_6, c_368])).
% 10.40/4.29  tff(c_27163, plain, (![B_411, B_412]: (k7_relat_1(B_411, k4_xboole_0(k1_relat_1(B_411), B_412))=k4_xboole_0(B_411, k7_relat_1(B_411, B_412)) | ~v1_relat_1(B_411) | ~v1_relat_1(B_411))), inference(superposition, [status(thm), theory('equality')], [c_378, c_768])).
% 10.40/4.29  tff(c_492, plain, (![A_26, A_81]: (k1_relat_1(k7_relat_1(k6_relat_1(A_26), A_81))=A_81 | ~r1_tarski(A_81, A_26) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_481])).
% 10.40/4.29  tff(c_504, plain, (![A_26, A_81]: (k1_relat_1(k7_relat_1(k6_relat_1(A_26), A_81))=A_81 | ~r1_tarski(A_81, A_26))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_492])).
% 10.40/4.29  tff(c_27247, plain, (![A_26, B_412]: (k1_relat_1(k4_xboole_0(k6_relat_1(A_26), k7_relat_1(k6_relat_1(A_26), B_412)))=k4_xboole_0(k1_relat_1(k6_relat_1(A_26)), B_412) | ~r1_tarski(k4_xboole_0(k1_relat_1(k6_relat_1(A_26)), B_412), A_26) | ~v1_relat_1(k6_relat_1(A_26)) | ~v1_relat_1(k6_relat_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_27163, c_504])).
% 10.40/4.29  tff(c_30033, plain, (![A_424, B_425]: (k1_relat_1(k4_xboole_0(k6_relat_1(A_424), k7_relat_1(k6_relat_1(A_424), B_425)))=k4_xboole_0(A_424, B_425))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_12, c_30, c_30, c_27247])).
% 10.40/4.29  tff(c_30294, plain, (![A_26, A_73]: (k4_xboole_0(A_26, A_73)=k1_relat_1(k4_xboole_0(k6_relat_1(A_26), k6_relat_1(A_26))) | ~r1_tarski(A_26, A_73))), inference(superposition, [status(thm), theory('equality')], [c_377, c_30033])).
% 10.40/4.29  tff(c_30382, plain, (![A_426, A_427]: (k4_xboole_0(A_426, A_427)=k1_xboole_0 | ~r1_tarski(A_426, A_427))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_144, c_30294])).
% 10.40/4.29  tff(c_30551, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_48, c_30382])).
% 10.40/4.29  tff(c_16, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.40/4.29  tff(c_30593, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_30551, c_16])).
% 10.40/4.29  tff(c_30609, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30593])).
% 10.40/4.29  tff(c_719, plain, (![C_93, A_94, B_95]: (k2_wellord1(k2_wellord1(C_93, A_94), B_95)=k2_wellord1(C_93, k3_xboole_0(A_94, B_95)) | ~v1_relat_1(C_93))), inference(cnfTransformation, [status(thm)], [f_79])).
% 10.40/4.29  tff(c_652, plain, (![C_90, B_91, A_92]: (k2_wellord1(k2_wellord1(C_90, B_91), A_92)=k2_wellord1(k2_wellord1(C_90, A_92), B_91) | ~v1_relat_1(C_90))), inference(cnfTransformation, [status(thm)], [f_83])).
% 10.40/4.29  tff(c_46, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_2'), '#skF_1')!=k2_wellord1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 10.40/4.29  tff(c_679, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_652, c_46])).
% 10.40/4.29  tff(c_712, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_679])).
% 10.40/4.29  tff(c_728, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_719, c_712])).
% 10.40/4.29  tff(c_764, plain, (k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))!=k2_wellord1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_728])).
% 10.40/4.29  tff(c_30746, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30609, c_764])).
% 10.40/4.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.40/4.29  
% 10.40/4.29  Inference rules
% 10.40/4.29  ----------------------
% 10.40/4.29  #Ref     : 0
% 10.40/4.29  #Sup     : 7256
% 10.40/4.29  #Fact    : 0
% 10.40/4.29  #Define  : 0
% 10.40/4.29  #Split   : 1
% 10.40/4.29  #Chain   : 0
% 10.40/4.29  #Close   : 0
% 10.40/4.29  
% 10.40/4.29  Ordering : KBO
% 10.40/4.29  
% 10.40/4.29  Simplification rules
% 10.40/4.29  ----------------------
% 10.40/4.29  #Subsume      : 1610
% 10.40/4.29  #Demod        : 9871
% 10.40/4.29  #Tautology    : 3987
% 10.40/4.29  #SimpNegUnit  : 0
% 10.40/4.29  #BackRed      : 1
% 10.40/4.29  
% 10.40/4.29  #Partial instantiations: 0
% 10.40/4.29  #Strategies tried      : 1
% 10.40/4.29  
% 10.40/4.29  Timing (in seconds)
% 10.40/4.29  ----------------------
% 10.40/4.29  Preprocessing        : 0.34
% 10.40/4.29  Parsing              : 0.18
% 10.40/4.29  CNF conversion       : 0.02
% 10.40/4.29  Main loop            : 3.14
% 10.40/4.29  Inferencing          : 0.77
% 10.40/4.29  Reduction            : 1.27
% 10.40/4.29  Demodulation         : 1.01
% 10.40/4.29  BG Simplification    : 0.10
% 10.40/4.29  Subsumption          : 0.87
% 10.40/4.29  Abstraction          : 0.15
% 10.40/4.30  MUC search           : 0.00
% 10.40/4.30  Cooper               : 0.00
% 10.40/4.30  Total                : 3.51
% 10.40/4.30  Index Insertion      : 0.00
% 10.40/4.30  Index Deletion       : 0.00
% 10.40/4.30  Index Matching       : 0.00
% 10.40/4.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
