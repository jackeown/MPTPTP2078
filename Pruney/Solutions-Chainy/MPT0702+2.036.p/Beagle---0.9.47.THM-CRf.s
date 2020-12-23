%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:05:07 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 194 expanded)
%              Number of leaves         :   26 (  81 expanded)
%              Depth                    :   15
%              Number of atoms          :  138 ( 481 expanded)
%              Number of equality atoms :   43 (  82 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(k9_relat_1(C,A),k9_relat_1(C,B))
            & r1_tarski(A,k1_relat_1(C))
            & v2_funct_1(C) )
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t157_funct_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( v2_funct_1(C)
       => k9_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t121_funct_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( v2_funct_1(B)
       => r1_tarski(k10_relat_1(B,k9_relat_1(B,A)),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_funct_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_38,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | k4_xboole_0(A_21,B_22) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_24])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_43,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_63,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_43])).

tff(c_82,plain,(
    ! [A_28,B_29] :
      ( k3_xboole_0(A_28,B_29) = A_28
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_102,plain,(
    ! [B_2] : k3_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_82])).

tff(c_160,plain,(
    ! [A_33,B_34] : k5_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = k4_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_172,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k4_xboole_0(B_2,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_160])).

tff(c_176,plain,(
    ! [B_2] : k5_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_172])).

tff(c_34,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_26,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_424,plain,(
    ! [C_56,A_57,B_58] :
      ( k3_xboole_0(k9_relat_1(C_56,A_57),k9_relat_1(C_56,B_58)) = k9_relat_1(C_56,k3_xboole_0(A_57,B_58))
      | ~ v2_funct_1(C_56)
      | ~ v1_funct_1(C_56)
      | ~ v1_relat_1(C_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_30,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_436,plain,
    ( k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_99])).

tff(c_465,plain,(
    k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k9_relat_1('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_436])).

tff(c_370,plain,(
    ! [B_50,A_51] :
      ( r1_tarski(k10_relat_1(B_50,k9_relat_1(B_50,A_51)),A_51)
      | ~ v2_funct_1(B_50)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_385,plain,(
    ! [B_50,A_51] :
      ( k4_xboole_0(k10_relat_1(B_50,k9_relat_1(B_50,A_51)),A_51) = k1_xboole_0
      | ~ v2_funct_1(B_50)
      | ~ v1_funct_1(B_50)
      | ~ v1_relat_1(B_50) ) ),
    inference(resolution,[status(thm)],[c_370,c_10])).

tff(c_480,plain,
    ( k4_xboole_0(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_385])).

tff(c_497,plain,(
    k4_xboole_0(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_480])).

tff(c_62,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_43])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k10_relat_1(B_17,k9_relat_1(B_17,A_16)),A_16)
      | ~ v2_funct_1(B_17)
      | ~ v1_funct_1(B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_189,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,k10_relat_1(B_37,k9_relat_1(B_37,A_36)))
      | ~ r1_tarski(A_36,k1_relat_1(B_37))
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1248,plain,(
    ! [B_75,A_76] :
      ( k10_relat_1(B_75,k9_relat_1(B_75,A_76)) = A_76
      | ~ r1_tarski(k10_relat_1(B_75,k9_relat_1(B_75,A_76)),A_76)
      | ~ r1_tarski(A_76,k1_relat_1(B_75))
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_189,c_2])).

tff(c_1456,plain,(
    ! [B_79,A_80] :
      ( k10_relat_1(B_79,k9_relat_1(B_79,A_80)) = A_80
      | ~ r1_tarski(A_80,k1_relat_1(B_79))
      | ~ v2_funct_1(B_79)
      | ~ v1_funct_1(B_79)
      | ~ v1_relat_1(B_79) ) ),
    inference(resolution,[status(thm)],[c_22,c_1248])).

tff(c_1467,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_1456])).

tff(c_1476,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_1467])).

tff(c_486,plain,
    ( r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_22])).

tff(c_501,plain,(
    r1_tarski(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_26,c_486])).

tff(c_1513,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1476,c_501])).

tff(c_14,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_103,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_116,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,k3_xboole_0(A_7,B_8)) ) ),
    inference(resolution,[status(thm)],[c_14,c_103])).

tff(c_1572,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1513,c_116])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( r1_tarski(A_14,k10_relat_1(B_15,k9_relat_1(B_15,A_14)))
      | ~ r1_tarski(A_14,k1_relat_1(B_15))
      | ~ v1_relat_1(B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_489,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_20])).

tff(c_503,plain,
    ( r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_489])).

tff(c_838,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_842,plain,(
    k4_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_838])).

tff(c_1589,plain,(
    k4_xboole_0('#skF_1',k1_relat_1('#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1572,c_842])).

tff(c_1598,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_1589])).

tff(c_1599,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_114,plain,(
    ! [B_4,A_3] :
      ( B_4 = A_3
      | ~ r1_tarski(B_4,A_3)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_103])).

tff(c_1708,plain,
    ( k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2')
    | k4_xboole_0(k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')),k3_xboole_0('#skF_1','#skF_2')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1599,c_114])).

tff(c_1719,plain,(
    k10_relat_1('#skF_3',k9_relat_1('#skF_3','#skF_1')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_1708])).

tff(c_1749,plain,
    ( r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1719,c_20])).

tff(c_1763,plain,(
    r1_tarski('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_28,c_1749])).

tff(c_1779,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1763,c_116])).

tff(c_12,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1814,plain,(
    k5_xboole_0('#skF_1','#skF_1') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1779,c_12])).

tff(c_1829,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_1814])).

tff(c_1831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_1829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.61  %$ r1_tarski > v2_funct_1 > v1_relat_1 > v1_funct_1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.61  
% 3.48/1.61  %Foreground sorts:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Background operators:
% 3.48/1.61  
% 3.48/1.61  
% 3.48/1.61  %Foreground operators:
% 3.48/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.48/1.61  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.61  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.61  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.61  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.48/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.61  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.61  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.48/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.61  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.61  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.48/1.61  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.48/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.61  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.48/1.61  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.48/1.61  
% 3.48/1.62  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.48/1.62  tff(f_78, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (((r1_tarski(k9_relat_1(C, A), k9_relat_1(C, B)) & r1_tarski(A, k1_relat_1(C))) & v2_funct_1(C)) => r1_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t157_funct_1)).
% 3.48/1.62  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.48/1.62  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.48/1.62  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.48/1.62  tff(f_51, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (v2_funct_1(C) => (k9_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t121_funct_1)).
% 3.48/1.62  tff(f_65, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (v2_funct_1(B) => r1_tarski(k10_relat_1(B, k9_relat_1(B, A)), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_funct_1)).
% 3.48/1.62  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 3.48/1.62  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.48/1.62  tff(c_38, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | k4_xboole_0(A_21, B_22)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.62  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_42, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_24])).
% 3.48/1.62  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.62  tff(c_43, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.62  tff(c_63, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_43])).
% 3.48/1.62  tff(c_82, plain, (![A_28, B_29]: (k3_xboole_0(A_28, B_29)=A_28 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.48/1.62  tff(c_102, plain, (![B_2]: (k3_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_82])).
% 3.48/1.62  tff(c_160, plain, (![A_33, B_34]: (k5_xboole_0(A_33, k3_xboole_0(A_33, B_34))=k4_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.62  tff(c_172, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k4_xboole_0(B_2, B_2))), inference(superposition, [status(thm), theory('equality')], [c_102, c_160])).
% 3.48/1.62  tff(c_176, plain, (![B_2]: (k5_xboole_0(B_2, B_2)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_63, c_172])).
% 3.48/1.62  tff(c_34, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_28, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_26, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_424, plain, (![C_56, A_57, B_58]: (k3_xboole_0(k9_relat_1(C_56, A_57), k9_relat_1(C_56, B_58))=k9_relat_1(C_56, k3_xboole_0(A_57, B_58)) | ~v2_funct_1(C_56) | ~v1_funct_1(C_56) | ~v1_relat_1(C_56))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.48/1.62  tff(c_30, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.48/1.62  tff(c_99, plain, (k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_82])).
% 3.48/1.62  tff(c_436, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_424, c_99])).
% 3.48/1.62  tff(c_465, plain, (k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k9_relat_1('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_436])).
% 3.48/1.62  tff(c_370, plain, (![B_50, A_51]: (r1_tarski(k10_relat_1(B_50, k9_relat_1(B_50, A_51)), A_51) | ~v2_funct_1(B_50) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.62  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.62  tff(c_385, plain, (![B_50, A_51]: (k4_xboole_0(k10_relat_1(B_50, k9_relat_1(B_50, A_51)), A_51)=k1_xboole_0 | ~v2_funct_1(B_50) | ~v1_funct_1(B_50) | ~v1_relat_1(B_50))), inference(resolution, [status(thm)], [c_370, c_10])).
% 3.48/1.62  tff(c_480, plain, (k4_xboole_0(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0 | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_465, c_385])).
% 3.48/1.62  tff(c_497, plain, (k4_xboole_0(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_480])).
% 3.48/1.62  tff(c_62, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_43])).
% 3.48/1.62  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k10_relat_1(B_17, k9_relat_1(B_17, A_16)), A_16) | ~v2_funct_1(B_17) | ~v1_funct_1(B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.48/1.62  tff(c_189, plain, (![A_36, B_37]: (r1_tarski(A_36, k10_relat_1(B_37, k9_relat_1(B_37, A_36))) | ~r1_tarski(A_36, k1_relat_1(B_37)) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.48/1.62  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.62  tff(c_1248, plain, (![B_75, A_76]: (k10_relat_1(B_75, k9_relat_1(B_75, A_76))=A_76 | ~r1_tarski(k10_relat_1(B_75, k9_relat_1(B_75, A_76)), A_76) | ~r1_tarski(A_76, k1_relat_1(B_75)) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_189, c_2])).
% 3.48/1.62  tff(c_1456, plain, (![B_79, A_80]: (k10_relat_1(B_79, k9_relat_1(B_79, A_80))=A_80 | ~r1_tarski(A_80, k1_relat_1(B_79)) | ~v2_funct_1(B_79) | ~v1_funct_1(B_79) | ~v1_relat_1(B_79))), inference(resolution, [status(thm)], [c_22, c_1248])).
% 3.48/1.62  tff(c_1467, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_1456])).
% 3.48/1.62  tff(c_1476, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_1467])).
% 3.48/1.62  tff(c_486, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_465, c_22])).
% 3.48/1.62  tff(c_501, plain, (r1_tarski(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_26, c_486])).
% 3.48/1.62  tff(c_1513, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1476, c_501])).
% 3.48/1.62  tff(c_14, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.48/1.62  tff(c_103, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.48/1.62  tff(c_116, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, k3_xboole_0(A_7, B_8)))), inference(resolution, [status(thm)], [c_14, c_103])).
% 3.48/1.62  tff(c_1572, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_1513, c_116])).
% 3.48/1.62  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.62  tff(c_20, plain, (![A_14, B_15]: (r1_tarski(A_14, k10_relat_1(B_15, k9_relat_1(B_15, A_14))) | ~r1_tarski(A_14, k1_relat_1(B_15)) | ~v1_relat_1(B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.48/1.62  tff(c_489, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_465, c_20])).
% 3.48/1.62  tff(c_503, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_489])).
% 3.48/1.62  tff(c_838, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_503])).
% 3.48/1.62  tff(c_842, plain, (k4_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_relat_1('#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_838])).
% 3.48/1.62  tff(c_1589, plain, (k4_xboole_0('#skF_1', k1_relat_1('#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1572, c_842])).
% 3.48/1.62  tff(c_1598, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_62, c_1589])).
% 3.48/1.62  tff(c_1599, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')))), inference(splitRight, [status(thm)], [c_503])).
% 3.48/1.62  tff(c_114, plain, (![B_4, A_3]: (B_4=A_3 | ~r1_tarski(B_4, A_3) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_103])).
% 3.48/1.62  tff(c_1708, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2') | k4_xboole_0(k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1')), k3_xboole_0('#skF_1', '#skF_2'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_1599, c_114])).
% 3.48/1.62  tff(c_1719, plain, (k10_relat_1('#skF_3', k9_relat_1('#skF_3', '#skF_1'))=k3_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_1708])).
% 3.48/1.62  tff(c_1749, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1719, c_20])).
% 3.48/1.62  tff(c_1763, plain, (r1_tarski('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_28, c_1749])).
% 3.48/1.62  tff(c_1779, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_1763, c_116])).
% 3.48/1.62  tff(c_12, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.48/1.62  tff(c_1814, plain, (k5_xboole_0('#skF_1', '#skF_1')=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1779, c_12])).
% 3.48/1.62  tff(c_1829, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_176, c_1814])).
% 3.48/1.62  tff(c_1831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_1829])).
% 3.48/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.62  
% 3.48/1.62  Inference rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Ref     : 0
% 3.48/1.62  #Sup     : 418
% 3.48/1.62  #Fact    : 0
% 3.48/1.62  #Define  : 0
% 3.48/1.62  #Split   : 5
% 3.48/1.62  #Chain   : 0
% 3.48/1.62  #Close   : 0
% 3.48/1.62  
% 3.48/1.62  Ordering : KBO
% 3.48/1.62  
% 3.48/1.62  Simplification rules
% 3.48/1.62  ----------------------
% 3.48/1.62  #Subsume      : 22
% 3.48/1.62  #Demod        : 452
% 3.48/1.62  #Tautology    : 206
% 3.48/1.62  #SimpNegUnit  : 1
% 3.48/1.62  #BackRed      : 34
% 3.48/1.62  
% 3.48/1.62  #Partial instantiations: 0
% 3.48/1.62  #Strategies tried      : 1
% 3.48/1.62  
% 3.48/1.62  Timing (in seconds)
% 3.48/1.62  ----------------------
% 3.90/1.63  Preprocessing        : 0.28
% 3.90/1.63  Parsing              : 0.16
% 3.90/1.63  CNF conversion       : 0.02
% 3.90/1.63  Main loop            : 0.57
% 3.90/1.63  Inferencing          : 0.19
% 3.90/1.63  Reduction            : 0.21
% 3.90/1.63  Demodulation         : 0.16
% 3.90/1.63  BG Simplification    : 0.02
% 3.90/1.63  Subsumption          : 0.11
% 3.90/1.63  Abstraction          : 0.03
% 3.90/1.63  MUC search           : 0.00
% 3.90/1.63  Cooper               : 0.00
% 3.90/1.63  Total                : 0.89
% 3.90/1.63  Index Insertion      : 0.00
% 3.90/1.63  Index Deletion       : 0.00
% 3.90/1.63  Index Matching       : 0.00
% 3.90/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
