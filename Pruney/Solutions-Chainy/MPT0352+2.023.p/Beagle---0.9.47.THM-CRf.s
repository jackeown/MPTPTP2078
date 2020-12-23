%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 134 expanded)
%              Number of leaves         :   24 (  54 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 206 expanded)
%              Number of equality atoms :   27 (  55 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_45,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_24,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_107,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_212,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_30])).

tff(c_20,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k3_subset_1(A_37,B_38)
      | ~ m1_subset_1(B_38,k1_zfmisc_1(A_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_108])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k2_xboole_0(B_9,C_10))
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_554,plain,(
    ! [C_56] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_56))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_8])).

tff(c_558,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_212,c_554])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_241,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_262,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_241])).

tff(c_125,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_108])).

tff(c_10,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_19,B_20] : k6_subset_1(A_19,B_20) = k4_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_15,B_16] : m1_subset_1(k6_subset_1(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [A_15,B_16] : m1_subset_1(k4_xboole_0(A_15,B_16),k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14])).

tff(c_114,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_subset_1(A_15,k4_xboole_0(A_15,B_16)) ),
    inference(resolution,[status(thm)],[c_31,c_108])).

tff(c_174,plain,(
    ! [A_42,B_43] : k3_subset_1(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_114])).

tff(c_183,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_174])).

tff(c_268,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_183])).

tff(c_156,plain,(
    ! [A_39,B_40,C_41] :
      ( r1_tarski(k4_xboole_0(A_39,B_40),C_41)
      | ~ r1_tarski(A_39,k2_xboole_0(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_739,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k3_xboole_0(A_69,B_70),C_71)
      | ~ r1_tarski(A_69,k2_xboole_0(k4_xboole_0(A_69,B_70),C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_156])).

tff(c_774,plain,(
    ! [C_71] :
      ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),C_71)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_71)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_739])).

tff(c_801,plain,(
    ! [C_72] :
      ( r1_tarski('#skF_2',C_72)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_774])).

tff(c_878,plain,(
    ! [A_75] :
      ( r1_tarski('#skF_2',A_75)
      | ~ r1_tarski('#skF_1',k2_xboole_0(A_75,k3_subset_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_801])).

tff(c_896,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_558,c_878])).

tff(c_912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_107,c_896])).

tff(c_914,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_915,plain,(
    ! [A_76,B_77] :
      ( k3_subset_1(A_76,k3_subset_1(A_76,B_77)) = B_77
      | ~ m1_subset_1(B_77,k1_zfmisc_1(A_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_927,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_22,c_915])).

tff(c_938,plain,(
    ! [A_78,B_79] :
      ( k4_xboole_0(A_78,B_79) = k3_subset_1(A_78,B_79)
      | ~ m1_subset_1(B_79,k1_zfmisc_1(A_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_955,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_22,c_938])).

tff(c_978,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_31])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1007,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_978,c_12])).

tff(c_1011,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_927,c_1007])).

tff(c_975,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_10])).

tff(c_1050,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1011,c_975])).

tff(c_103,plain,(
    ! [A_34,B_35,C_36] :
      ( r1_tarski(A_34,k2_xboole_0(B_35,C_36))
      | ~ r1_tarski(k4_xboole_0(A_34,B_35),C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1489,plain,(
    ! [A_107,B_108,C_109] :
      ( r1_tarski(A_107,k2_xboole_0(k4_xboole_0(A_107,B_108),C_109))
      | ~ r1_tarski(k3_xboole_0(A_107,B_108),C_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_103])).

tff(c_1520,plain,(
    ! [C_109] :
      ( r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_109))
      | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),C_109) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_955,c_1489])).

tff(c_1564,plain,(
    ! [C_111] :
      ( r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_111))
      | ~ r1_tarski('#skF_2',C_111) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1520])).

tff(c_1629,plain,(
    ! [B_115] :
      ( r1_tarski('#skF_1',k2_xboole_0(B_115,k3_subset_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',B_115) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1564])).

tff(c_954,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_20,c_938])).

tff(c_991,plain,(
    ! [A_80,B_81,C_82] :
      ( r1_tarski(k4_xboole_0(A_80,B_81),C_82)
      | ~ r1_tarski(A_80,k2_xboole_0(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1164,plain,(
    ! [C_87] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_87)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_87)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_954,c_991])).

tff(c_913,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_1168,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_1164,c_913])).

tff(c_1644,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_1629,c_1168])).

tff(c_1659,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_914,c_1644])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:40:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  
% 3.24/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  %$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.61  
% 3.24/1.61  %Foreground sorts:
% 3.24/1.61  
% 3.24/1.61  
% 3.24/1.61  %Background operators:
% 3.24/1.61  
% 3.24/1.61  
% 3.24/1.61  %Foreground operators:
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.61  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.61  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.24/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.24/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.61  
% 3.24/1.63  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_subset_1)).
% 3.24/1.63  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.24/1.63  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 3.24/1.63  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.24/1.63  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.24/1.63  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.24/1.63  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.24/1.63  tff(f_45, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.24/1.63  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 3.24/1.63  tff(c_24, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.63  tff(c_107, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_24])).
% 3.24/1.63  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.63  tff(c_212, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_107, c_30])).
% 3.24/1.63  tff(c_20, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.63  tff(c_108, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k3_subset_1(A_37, B_38) | ~m1_subset_1(B_38, k1_zfmisc_1(A_37)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.63  tff(c_124, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_108])).
% 3.24/1.63  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k2_xboole_0(B_9, C_10)) | ~r1_tarski(k4_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.63  tff(c_554, plain, (![C_56]: (r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_56)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_56))), inference(superposition, [status(thm), theory('equality')], [c_124, c_8])).
% 3.24/1.63  tff(c_558, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_212, c_554])).
% 3.24/1.63  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.63  tff(c_22, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.63  tff(c_241, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.63  tff(c_262, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_241])).
% 3.24/1.63  tff(c_125, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_108])).
% 3.24/1.63  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.24/1.63  tff(c_18, plain, (![A_19, B_20]: (k6_subset_1(A_19, B_20)=k4_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.24/1.63  tff(c_14, plain, (![A_15, B_16]: (m1_subset_1(k6_subset_1(A_15, B_16), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.63  tff(c_31, plain, (![A_15, B_16]: (m1_subset_1(k4_xboole_0(A_15, B_16), k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14])).
% 3.24/1.63  tff(c_114, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_subset_1(A_15, k4_xboole_0(A_15, B_16)))), inference(resolution, [status(thm)], [c_31, c_108])).
% 3.24/1.63  tff(c_174, plain, (![A_42, B_43]: (k3_subset_1(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_114])).
% 3.24/1.63  tff(c_183, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_125, c_174])).
% 3.24/1.63  tff(c_268, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_262, c_183])).
% 3.24/1.63  tff(c_156, plain, (![A_39, B_40, C_41]: (r1_tarski(k4_xboole_0(A_39, B_40), C_41) | ~r1_tarski(A_39, k2_xboole_0(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.63  tff(c_739, plain, (![A_69, B_70, C_71]: (r1_tarski(k3_xboole_0(A_69, B_70), C_71) | ~r1_tarski(A_69, k2_xboole_0(k4_xboole_0(A_69, B_70), C_71)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_156])).
% 3.24/1.63  tff(c_774, plain, (![C_71]: (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), C_71) | ~r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_71)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_739])).
% 3.24/1.63  tff(c_801, plain, (![C_72]: (r1_tarski('#skF_2', C_72) | ~r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_72)))), inference(demodulation, [status(thm), theory('equality')], [c_268, c_774])).
% 3.24/1.63  tff(c_878, plain, (![A_75]: (r1_tarski('#skF_2', A_75) | ~r1_tarski('#skF_1', k2_xboole_0(A_75, k3_subset_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_801])).
% 3.24/1.63  tff(c_896, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_558, c_878])).
% 3.24/1.63  tff(c_912, plain, $false, inference(negUnitSimplification, [status(thm)], [c_107, c_896])).
% 3.24/1.63  tff(c_914, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 3.24/1.63  tff(c_915, plain, (![A_76, B_77]: (k3_subset_1(A_76, k3_subset_1(A_76, B_77))=B_77 | ~m1_subset_1(B_77, k1_zfmisc_1(A_76)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.63  tff(c_927, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_22, c_915])).
% 3.24/1.63  tff(c_938, plain, (![A_78, B_79]: (k4_xboole_0(A_78, B_79)=k3_subset_1(A_78, B_79) | ~m1_subset_1(B_79, k1_zfmisc_1(A_78)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.63  tff(c_955, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_22, c_938])).
% 3.24/1.63  tff(c_978, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_955, c_31])).
% 3.24/1.63  tff(c_12, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.63  tff(c_1007, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_978, c_12])).
% 3.24/1.63  tff(c_1011, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_927, c_1007])).
% 3.24/1.63  tff(c_975, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_955, c_10])).
% 3.24/1.63  tff(c_1050, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1011, c_975])).
% 3.24/1.63  tff(c_103, plain, (![A_34, B_35, C_36]: (r1_tarski(A_34, k2_xboole_0(B_35, C_36)) | ~r1_tarski(k4_xboole_0(A_34, B_35), C_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.63  tff(c_1489, plain, (![A_107, B_108, C_109]: (r1_tarski(A_107, k2_xboole_0(k4_xboole_0(A_107, B_108), C_109)) | ~r1_tarski(k3_xboole_0(A_107, B_108), C_109))), inference(superposition, [status(thm), theory('equality')], [c_10, c_103])).
% 3.24/1.63  tff(c_1520, plain, (![C_109]: (r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_109)) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), C_109))), inference(superposition, [status(thm), theory('equality')], [c_955, c_1489])).
% 3.24/1.63  tff(c_1564, plain, (![C_111]: (r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_111)) | ~r1_tarski('#skF_2', C_111))), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1520])).
% 3.24/1.63  tff(c_1629, plain, (![B_115]: (r1_tarski('#skF_1', k2_xboole_0(B_115, k3_subset_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', B_115))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1564])).
% 3.24/1.63  tff(c_954, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_20, c_938])).
% 3.24/1.63  tff(c_991, plain, (![A_80, B_81, C_82]: (r1_tarski(k4_xboole_0(A_80, B_81), C_82) | ~r1_tarski(A_80, k2_xboole_0(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.63  tff(c_1164, plain, (![C_87]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_87) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_87)))), inference(superposition, [status(thm), theory('equality')], [c_954, c_991])).
% 3.24/1.63  tff(c_913, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_24])).
% 3.24/1.63  tff(c_1168, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_1164, c_913])).
% 3.24/1.63  tff(c_1644, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_1629, c_1168])).
% 3.24/1.63  tff(c_1659, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_914, c_1644])).
% 3.24/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.63  
% 3.24/1.63  Inference rules
% 3.24/1.63  ----------------------
% 3.24/1.63  #Ref     : 0
% 3.24/1.63  #Sup     : 420
% 3.24/1.63  #Fact    : 0
% 3.24/1.63  #Define  : 0
% 3.24/1.63  #Split   : 1
% 3.24/1.63  #Chain   : 0
% 3.24/1.63  #Close   : 0
% 3.24/1.63  
% 3.24/1.63  Ordering : KBO
% 3.24/1.63  
% 3.24/1.63  Simplification rules
% 3.24/1.63  ----------------------
% 3.24/1.63  #Subsume      : 29
% 3.24/1.63  #Demod        : 271
% 3.24/1.63  #Tautology    : 248
% 3.24/1.63  #SimpNegUnit  : 3
% 3.24/1.63  #BackRed      : 6
% 3.24/1.63  
% 3.24/1.63  #Partial instantiations: 0
% 3.24/1.63  #Strategies tried      : 1
% 3.24/1.63  
% 3.24/1.63  Timing (in seconds)
% 3.24/1.63  ----------------------
% 3.24/1.63  Preprocessing        : 0.31
% 3.24/1.63  Parsing              : 0.17
% 3.24/1.63  CNF conversion       : 0.02
% 3.24/1.63  Main loop            : 0.50
% 3.24/1.63  Inferencing          : 0.18
% 3.24/1.63  Reduction            : 0.18
% 3.24/1.63  Demodulation         : 0.14
% 3.24/1.63  BG Simplification    : 0.02
% 3.24/1.63  Subsumption          : 0.07
% 3.24/1.63  Abstraction          : 0.03
% 3.24/1.63  MUC search           : 0.00
% 3.24/1.63  Cooper               : 0.00
% 3.24/1.63  Total                : 0.84
% 3.24/1.63  Index Insertion      : 0.00
% 3.24/1.63  Index Deletion       : 0.00
% 3.24/1.63  Index Matching       : 0.00
% 3.24/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
